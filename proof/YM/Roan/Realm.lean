import YM.Roan.Africa
import YM.Roan.Croft
import YM.Roan.Wire
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open Filter Function Set Lattice Wilson RG Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Poised Poised.Beacon Poised.Display Poised.Stative Poised.Sieve
open Finset Tawny Tawny.Cast Tawny.Cast.Rays Tawny.Cast.Carnal Tawny.Cast.TableT Tawny.Pane Tawny.BendR
open Oriole Counting Counting.Click PCAC Patria.Gall.Seals Patria.Gall
-- incomes cost norm.S
local notation "Z"=> RawVec 10
set_option quotPrecheck false
variable (u a α ε L Q M B C D θ e x b eΛ g t₀ R:ℝ)
variable (n:ℕ)(Pt:ℕ→BudgetPoint)(A V:ℕ→ℝ)
-- Faith = dependencies; later choose posts. b upper root derivative,money, flux_B0
local notation "D0"=> D*(C*M)
local notation "De"=> D*(C*e)
local notation "eM" p:arg=> 6*p
/-- b cross pivot cap; x accuracy after correction. e recurrence errors/reading errs upper each ≤e. g≤ limit for coefficients normalized by t* (budget); eΛ:= leeway for det gap on physically reflected kernel.Per-axis.
-/
structure Pueblo :Prop where
       cal:0 < e
       sig: Signature C D
       north: FundX u a α ε (L^4) (L^5) M B θ e n
       ca: 0 < eΛ
       cc:1 ≤ b
       fuel: 2*(D*C*M)+eΛ ≤ b
       first: D*C*e+ e+ eΛ ≤x
       safety: 6*x ≤ 1/4
       yaw: (6*x)*(24*b)≤1/4
       graft: 100*b*(D*C*e+ e)≤g
       lift: g ≤1
       earn : 2*t₀* (D*C*M)+ (D*C*e) + 3*e + 2*(6*(2*(D*C*M))*g)+ (1+6:ℝ)*eΛ ≤ x
#print Pueblo
variable (p t:ℕ→Z)(Qv S:Flavor 6→ℕ→Z) (hp:Pueblo u a α ε L M B C D θ e x b eΛ g t₀ n) -- order need fields explicitly.L.
local notation "A0"=> (A n)^2
local notation "u₀"=> (Pt n).threshold
local notation "S0"=> (Pt n).threshold*(A n)^2
local notation "EA"=> fun i:Flavor 6=> Qv i 0
local notation "EZ"=> fun i:Flavor 6=> S i 0
local notation "rZ"=> Pi.single
local notation "BT" i:arg=> cashR (L^4) A0 n i
local notation "KT" i:arg=> cashR (L^4) S0 n i
variable (hV:∀ i,0 < A i) (hL:3 ≤ L)
local notation "FQ"=>Flavor 6→ℂ
local notation "uδ"=> compass (BT 0) (A 0)
local notation "wδ"=> torque (BT 0) (A 0)
include hp hV hL
lemma pivL (ht:∀ i, GlowZ (L^4) M C D e Pt A n A0 (Qv i))(hs:∀ i,GlowZ (L^4) M C D e Pt A n A0 (S i))(hh: ∀ i: Flavor 6,‖prismA (Qv i n)-rZ i 1‖≤e)(hk:∀ i:Flavor 6,(axM 0) (S i n)= rZ i 1∧ prismA (S i n)=0): SplitX EA EZ uδ wδ x b :=by
       have hΛ:0 ≤eΛ:=hp.ca.le; have he : De+e+eΛ≤x:=(add_le_add_left (add_le_add_left (show De=D*C*e from by ring).le _) _).trans hp.first; have htH:=zero_le_one.trans hp.sig.ng; have hC:=zero_le_one.trans hp.sig.pos
       have h:e≤x:=(le_add_of_nonneg_left (show 0≤De from by positivity [hp.cal])).trans ((le_add_of_nonneg_right hΛ).trans he)
       have he': De+e≤x:=(le_add_of_nonneg_right (show 0≤eΛ from hp.ca.le)).trans he; have hc:= hV n; have hu: 0 < L:= lt_of_lt_of_le (by norm_num) hL; have hg:= (cash_κ (L^4) A0 (by positivity) (by positivity) n).2.2
       have hq: D0 ≤ b:= by have hm :0 < M:=hp.north.m_ng; nlinarith only [hΛ,hp.fuel,show (C*M)≥0 from mul_nonneg hC hm.le,show D0≥0 from by positivity]
       refine ⟨hp.cal.le.trans h,hp.cc,hp.safety,hp.yaw,fun i=>?_ ,fun i=>(ht i).h0.trans hq,fun i=>?_ ,fun i=>?_⟩
       · have hp:= (ht i).Δ; rw [hg,(oR_t (A n) _ hc ((Pt n).threshold_pos) _).1] at hp; change ‖(uδ) _-_‖ ≤ x; exact (norm_sub_le_norm_sub_add_norm_sub ((uδ) _) (prismA (Qv i n)) _).trans ((add_le_add hp (hh _)).trans he')
       · have hf:= (hs i).h; rw [hg,(oR_t (A n) _ hc ((Pt n).threshold_pos) _).2.1,(hk _).1] at hf; exact hf.trans ((le_add_of_nonneg_right hp.cal.le).trans he')
       · have hf:= (hs i).Δ; rw [hg,(oR_t (A n) _ hc ((Pt n).threshold_pos) _).1,(hk _).2,sub_zero] at hf; exact hf.trans ((le_add_of_nonneg_right hp.cal.le).trans he')
lemma multip (x:Z)(t₁:ℕ)(hv:0 < A n): 
       (compass (BT t₁) (A t₁)) x= (↑u₀:ℂ) • compass (KT t₁) (A t₁) x ∧ (torque (BT t₁) (A t₁)) x= (↑u₀:ℂ) • torque (KT t₁) (A t₁) x:=by
         have hp: BT t₁=u₀ * KT t₁:=by unfold cashR; have ht:= (Pt n).threshold_pos; have hz:= sq_pos_of_pos hv; field_simp
         rw[hp]; unfold compass torque signature; simp only [LinearMap.smul_apply,smul_smul]; rw [mul_assoc]; push_cast; exact ⟨rfl,rfl⟩
local notation "blend" f:arg p:arg r:arg => Qv r
set_option maxHeartbeats 1000000 in
lemma compactG (X: GlowZ (L^4) M C D e Pt A n S0 p)(ht: SplitX EA EZ uδ wδ x b)(hA:‖prismA (p n)‖≤ u₀ * e)(hs:‖(axM 0) (p n)‖≤u₀ * e):∃ f v:FQ,‖(f,v)‖≤ g*u₀ ∧ bet 0 (p 0+ doubleW EA EZ (f,v))=0:=by
       have hC:=hp.sig.pos; have hl:0<L:=lt_of_lt_of_le (by norm_num) hL; have hu:= (Pt n).threshold_pos; have hP:A0>0:=sq_pos_of_pos (hV n); let r:=De; let W:= uδ; let K:=wδ; let A':=W (p 0); let B':=K (p 0); let x':=compass (KT 0) (A 0) (p 0); let y':=torque (KT 0) (A 0) (p 0)
       have ht1:= (cash_κ (L^4) S0 (by positivity) (by positivity) n).2.2; let E:=prismA (p n); let T:=(axM 0) (p n); have hG:= (oR_t (A n) u₀ (hV n) hu (p n)).2.2.2
       let z:ℝ:=u₀; let Z':ℂ:=(z⁻¹:ℝ); have he(t:FQ)(he: ‖t‖≤z*e): ‖Z' • t‖ ≤e:=by rw [norm_smul,show ‖Z'‖=z⁻¹ from (by unfold Z'; rw[Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hu.le)])]; exact (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hu.le)).trans_eq (by rw[←mul_assoc,inv_mul_cancel₀ hu.ne',one_mul])
       have hk: ‖(x',y')‖ ≤r+e:=by
            apply max_le; · exact ((norm_le_norm_sub_add ..).trans (add_le_add (show ‖x'-Z' • E‖ ≤ r from (by have h:= X.Δ; rw[ht1,hG.1] at h; exact h)) (he E hA)))
            exact ((norm_le_norm_sub_add ..).trans (add_le_add (show ‖y'- Z' • T‖ ≤ r from (by have h:= X.h; rw[ht1,hG.2] at h; exact h)) (he T hs)))
       obtain ⟨f,q,h1,h2,h3⟩:= voices ht (-A') (-B')
       have h': (A',B')=(z:ℂ) • (x',y'):=by change (A',B')= (((z:ℂ) • x'),((z:ℂ) • y')); simpa only [Prod.mk.injEq] using multip u a α ε L M B C D θ e x b eΛ g t₀ n Pt A hp hV hL (p 0) 0 (hV n) -- order/smul_prod
       have hf:= mul_nonneg (by norm_num:(0:ℝ)≤100) (zero_le_one.trans ht.cap)
       refine ⟨f,q,h3.trans (?_ : _ ≤_), (zeroJ _).2 ⟨?_, ?_⟩⟩
       · rw [show (-A', -B')=-(A',B') from rfl,norm_neg,h',norm_smul,Complex.norm_real,Real.norm_of_nonneg hu.le]
         refine ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk hu.le) hf)).trans ?_; unfold r; rw [show 100*b*(z*_)= (100*b*(D*C*e+e))*z from by ring]; exact mul_le_mul_of_nonneg_right hp.graft hu.le
       · have he : K (p 0+ doubleW EA EZ (f,q))=0:=by rw [map_add,show K (doubleW EA EZ (f,q))= -B' from h2]; exact add_neg_cancel (B')
         exact (_root_.smul_eq_zero.mp (show (↑(BT 0*(A 0)^2):ℂ) • ((axM 0) (p 0+doubleW EA EZ (f,q)))=0 from he)).resolve_left (by exact_mod_cast (show BT 0*(A 0)^2≠0 from (mul_pos ((cash_κ (L^4) _ (by positivity) hP _).1 _) (sq_pos_of_pos (hV 0))).ne'))
       have he: W (p 0+doubleW EA EZ (f,q))=0:=by rw[map_add,show W (doubleW EA EZ (f,q))=-A' from h1]; exact add_neg_cancel (A')
       rw[←baseA]; exact (_root_.smul_eq_zero.mp (show (↑(BT 0*(A 0)^2):ℂ) • (prismA (p 0+doubleW EA EZ (f,q)))=0 from he)).resolve_left (by exact_mod_cast (show BT 0*(A 0)^2 ≠0 from (mul_pos ((cash_κ (L^4) _ (by positivity) hP _).1 _) (sq_pos_of_pos (hV 0))).ne'))
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.compactG
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.pivL
