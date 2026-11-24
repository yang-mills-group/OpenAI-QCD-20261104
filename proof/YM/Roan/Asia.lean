import YM.Roan.Mesh
import YM.Kai.Nines
/-! Canonical costs.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MassiveQCD.Sample.Basal.Surge
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove Cupola Plate Card Iris
open MassiveQCD.Sample.LoomT Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.UV Stative Massive.Poised.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Stamp
variable {c f L:Side}{v t x δ α β κ ρ C C' ξ M B3 G3 σ B1 G1 a D_:ℝ}{P:BudgetPoint}{k n l m N:ℕ}
open QCD.Ruby Cove NormedSpace
open Massive.PCAC Massive.PCAC.Oren WindowU
local notation "b₂"=>(25/256:ℝ)
local notation "τ"=>(1/512:ℝ)
local notation "b₁"=>(24/256:ℝ)
local notation "b₀"=>(1/8:ℝ)
local notation "ε"=>(1/256:ℝ)
-- Pe Year Uniform startup, after wallet allowable H0=l.slot; κ estimated by scheduler below. caps.h.J
open Rates
variable (nF kF pF nL kL iF:ℕ)(vM vT At M₀ Ξ₀:ℝ)
variable (B:ℕ)
local notation "U★"=> prepV nF kF pF iF At M₀ B
local notation "V★" B:arg=> trekV nF kF pF iF At M₀ vT 0 B
local notation "cM"=>M₀ + 6*(M₀+M₀)
local notation "Sp" B:arg=> riseP nL kL B ε b₁
local notation "Fp" B:arg=> Stags.bonus nF B ε
local notation "aτ"=> P.threshold
variable (A γ eβ βh γ₀:ℝ) -- UC=A.T, H0=A/S, AF.
local notation "sc"=> Real.exp (b₁-b₀)
noncomputable def expense (B:ℕ):ℝ:=let F:= V★ B; let S:= Sp B; let q:= (1-sc)⁻¹ ; 1+ F*(4*q)+(a+(1+κ*a))*(F*S)*γ -- using Q=T Room ∈[A/4,4A]
#print expense
local notation "Kz" B:arg => expense nF kF pF nL kL iF vT At M₀ γ B (a:=a) (κ:=κ) -- fields a κ implicit? variables order.
open Finset
lemma funded_x : Fuel (fun B=> Kz B):=by
      have h := cost_traits nF kF pF nL kL iF vT At M₀; unfold expense; dsimp only; repeat' first | exact h.1|exact h.2.1|exact Fuel.cons _| apply Fuel.add| apply Fuel.mul
local notation "TK"=> (A/γ)
variable (M2 T1 H Pp Q:ℝ)
variable (h:P.order=kF)(h₁:P.power=pF)(h₂:P.B=B)(hz0:0≤M₀)(ht:0≤vT)(he:0≤At)(ha:0≤a)(hb:0≤κ)(hr:1≤γ)
lemma sc_lt: 0<sc ∧ sc<1:=⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by norm_num)⟩
include ha hb ht he hz0 hr
lemma toll_pos : 1 ≤ Kz B:=by
       unfold expense; dsimp only; have h := supple nF kF pF iF vT At M₀ B hz0 ht he; have hx:= inv_nonneg.mpr (sub_nonneg.mpr sc_lt.2.le); have hp:0 ≤ Sp B:=by unfold riseP polyPrice; positivity
       apply le_trans (b:=1+(V★ B)*(4*(1-sc)⁻¹)) (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_right (by positivity))
local notation "ηp"=> (A/H)
local notation "χ"=> (ubi P nF T1 ηp Pp Q B1)
local notation "φY"=> (foe P nL kL χ)
local notation "φQ"=> (ubi P nF T1 ηp Pp Q G1)
include h h₁ h₂
lemma rightCap (u:ℝ)(hU:0≤u)(hH:0<H)(hA:0<A)(hW:T1≤ cM)(hα:H ≥ Kz B*u)(hP:χ ≤ V★ B*ηp*u)(hL:A/4 ≤Q)(hV:φQ≤1) (hY:0≤χ)(hπ:hullP B nF*(Real.exp (b₂+τ)*(cM*ηp*2^kF)) ≤τ)(hΨ:(Fp B)*(1+κ*a)* TK* (Sp B) *γ ≤1) :Capital P nF nL kL a κ T1 ηp Pp Q B1 G1 TK:=by
       let p:=nF; let S:=Sp B; let C:=Kz B; let U:=V★ B; let q:=(1-sc)⁻¹; let t:=ηp; let Y:= TK; let φ:=χ; let F:= φY; have hu:0 ≤ U:= supple nF kF pF iF vT At M₀ B hz0 ht he; have hq:0 < 1-sc:= sub_pos.mpr sc_lt.2; have hp:0 < q:= inv_pos.mpr hq; have ht:0 ≤ t:=div_nonneg hA.le hH.le; have hS:0 ≤ S:=by unfold S riseP polyPrice; positivity
       have hφ:F=S*φ:=by unfold F S foe; rw[h₂]
       have hσ: t*H=A:= div_mul_cancel₀ _ hH.ne'
       have hf:0 ≤ (1+κ*a):=by positivity
       have hc : 0 ≤ sSup ({1}:Set ℝ):=by simp
       have hh:0 < γ:= zero_lt_one.trans_le hr; let W:= 1+κ*a
       have hs:0 ≤ (a+W)*(U*S)*γ:=mul_nonneg (mul_nonneg (add_nonneg ha hf) (mul_nonneg hu hS)) hh.le
       have h₀:U*(4*q) ≤C:= by change _ ≤ 1+U*(4*q) + (a+W)*(U*S)*γ; exact (le_add_of_nonneg_left zero_le_one).trans (le_add_of_nonneg_right hs)
       have hδ : W*(U*S)*γ ≤ C ∧ a*(U*S)*γ ≤C:=by
             have hx:0 ≤ 1+U*(4*q):=by positivity
             have hv: (a+W)*(U*S)*γ ≤ C := le_add_of_nonneg_left hx
             exact ⟨(mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ha) (mul_nonneg hu hS)) hh.le).trans hv,(mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hf) (mul_nonneg hu hS)) hh.le).trans hv⟩
       have hk:(4*q) * φ ≤ A:=by
             refine ((mul_le_mul_of_nonneg_left hP (mul_nonneg (by norm_num:(0:ℝ) ≤4) hp.le)).trans ?_); calc
               4*q*((V★ B)*(A/H)*u)= t*(U*(4*q)*u):=by unfold t U; ring
               _ ≤ t*H := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right h₀ hU).trans hα) ht
               _ = A:=hσ
       have hq' : φ≤ (1-sc)*(A/4):=by
             rw [← _root_.div_le_one (show 0<(1-sc)*(A/4) from by positivity)]
             have hφ: φ/((1-sc)*(A/4))=(4*q*φ)/A:=by unfold q; rw [inv_eq_one_div]; field_simp
             rw[hφ]; exact (_root_.div_le_one hA).mpr hk
       have hM':φ≤ A:=by calc
              φ ≤ (1-sc)*(A/4):=hq'
              _ ≤ 1*(A/4):= mul_le_mul_of_nonneg_right (by linarith only [sc_lt.1]) (by positivity)
              _ ≤A:=by linarith only [hA]
       have hK(u':ℝ)(hr':0≤u')(hp': u'*(U*S)*γ ≤ C): u'*F ≤ Y:=by
             apply (le_div_iff₀ hh).mpr; rw [hφ]
             calc u'*(S*φ)*γ ≤ u'*(S*(U*t*u))*γ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP hS) hr') hh.le
                  _ = t*((u'*(U*S)*γ)*u):=by ring
                  _ ≤ t*H := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hp' hU).trans hα) ht
                  _ = A:=hσ
       refine ⟨?_,hY,?_,hV,?_,hK _ hf hδ.1,hK _ ha hδ.2⟩
       · rw[h,h₂]; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hW ht) (by positivity)) (by positivity)) (show 0≤hullP B nF from by unfold hullP; positivity)).trans hπ
       · change Stags.bonus nF P.B ε*(F+κ*(a*F)) ≤1
         rw[h₂,hφ]; let p:=Fp B
         have hz:0 ≤ p:= earnB .. ; apply le_trans (b:= p*W*Y*S*γ) _ hΨ
         have hY : Y*γ= A:=div_mul_cancel₀ _ hh.ne'
         calc _ = (p*W*S)*φ:=by unfold W p; ring
              _ ≤ (p*W*S)*A := mul_le_mul_of_nonneg_left hM' (mul_nonneg (mul_nonneg hz hf) hS)
              _ = p*W*Y*S*γ:=by rw [←hY]; ring
       have h:= hq'.trans (mul_le_mul_of_nonneg_left hL hq.le); change _+ φ ≤_; nlinarith only [h]
-- Cap_from T and rank-derived costs. end
end YM.MassiveQCD.Sample.Basal.Surge
#print axioms YM.MassiveQCD.Sample.Basal.Surge.rightCap
#print axioms YM.MassiveQCD.Sample.Basal.Surge.funded_x
