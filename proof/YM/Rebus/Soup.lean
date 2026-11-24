import YM.Rebus.Shocks
import YM.Rebus.Veer
import YM.Play.Cause
import YM.Cape.Peace
/-! # Common ownership W. Awakening exact by Brief. Calculus upcoming. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Rebus
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Cape Play Play.Chamber QCD.Bera QCD.Anomaly Hypnos Hypnos.Fruit Rot
open Play.Camp
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{J K':Patch}{P:Teller su}{β x C μ W:ℝ}
variable {O:BudgetPoint}{ι κ I Z E D:Type}[Fintype I]
variable {N i j n k m l r t M B Q:ℕ}
section
namespace Rift
variable {t t' u u' s s' h h' v v' c r e:ℝ}{W₀ h₈ Λ D D' K Y Y' Ψ A:ℝ→ℝ}
open Bera.Oce Apron.Grove
-- fixed after stage Layer bed. v'≥r max tracked choose Hank before pass. Use V threshold POM proof. Forecast required each wall.Cap financed any ancestor.V
lemma coastRate : Rate su L 0 A → Rate su L 0 (fun i=>Chamber.face l (A i)):=fun h=>(powV h _).mul_left _
lemma cirRate (h: Rate su L 0 A) : Rate su L 0 (fun i=>expat n (A i) r):=(powV h _).mul_right _
lemma carousel (L:Side) : Rate su L 0 (fun i=> whirl l (radiusB i)):=by
    unfold whirl; push_cast; exact (powV (((Rate.radius_price.mul_left _).add (Rate.radius_price.mul_left _)).add (Rate.const _)) 4).mul_left _
-- Supp.W choose deterministic separation constant.Families costs path fixed upper M1.Reta. ζ=Ration.v actual ≤κ bound. use tributary with κ arbitrary ≤B.Es verify. Need show due.E ≤ a'x ε + b β.^. Use h compile X constants.Exp.
lemma freightRate {C:ℝ} (w:ℝ)(u:ℝ→ℝ) (htK:Rate su L 0 u)(hv:Rate su L (-3) W₀) (h:Rate su L 0 Y)(hC:Rate su L 0 h₈)(he:Rate su L (-(1/32)) Y')(hz:Rate su L (-(1/32)) D)(hd:Rate su L (-(1/32)) D') : Rate su L (-(1/32)) (fun i=> tributary l n m (radiusB i) w C (h₈ i) (Y i) (u i) (D i) (D' i) (Y' i) (betaF su i L) (W₀ i) 0) :=by
     unfold tributary chipE blowP; apply Rate.add
     · apply Rate.add
       · unfold snap; simp_rw [mul_zero,zero_add]; apply Rate.add
         · exact (pmul (pmul (hd.mul_left _) (powV htK _)) h).mul_left _
         exact pmul hz (pmul (powV htK _) h)
       have ht:Rate su L (-3) (fun i=> whirl l (radiusB i) * W₀ i):=pmul' hv (carousel L); have hi:Rate su L (-1) (fun i=> (betaF su i L)⁻¹):=by simpa only [Real.rpow_neg_one] using Rate.power (G:=su) (L:=L) (a:= -1)
       exact ((ht.mul_right _).weaken (by norm_num)).add (pmul (((ht.mul Rate.hat).weaken (by norm_num)).add ((pmul hi (cirRate htK)).weaken (by norm_num))) (h.mul_left _))
     exact pmul' (pmul (he.mul_left _) h) (powV htK _)
def debt0 (l k m:ℕ)(A h₈ C:ℝ):=mead (l*m) C*(Chamber.face l (A^(l*k)*h₈+1))
-- same on mixed 
lemma linearŪ (κ C hC h D D' θ A b t ε:ℝ): tributary l k m B κ C hC h A D D' θ t b ε= tributary l k m B κ C hC h A D D' θ t b 0+debt0 l k m A hC C*ε:=by unfold tributary Apron.Grove.chipE Apron.Grove.snap debt0; ring
-- cost_over anything.W Real D.S `sα` chosen upper ≥ pol profile anywhere.Month. 
def debt1 (l k m:ℕ)(A h₈ C S W:ℝ):ℝ:= W^l*((Chamber.face l S+1)^l*debt0 l k m A h₈ C)
lemma tariff0 (l k m:ℕ)(A h₈ C S W p q ε:ℝ): W^l * uCredit l m S q (p+debt0 l k m A h₈ C*ε)= W^l*uCredit l m S q p+debt1 l k m A h₈ C S W*ε:=by unfold uCredit debt1; ring
lemma freightP {C A:ℝ→ℝ}{Z:ℝ} (hW:Rate su L 0 W₀)(he:Rate su L 0 C) (h:Rate su L t D)(hd:Rate su L t Y') : Rate su L t (fun i=> W₀ i ^l*uCredit l k (C i) (D i) (Y' i)):=pmul' ((h.mul_left _|>.mul_right _).add (pmul' hd (powV ((coastRate he).add (Rate.const _)) _))) (powV hW _)
lemma pr (l k m B:ℕ)(c A h v ζ K C D D' θ t b ε:ℝ) (hC:1 ≤c)(hk:1 ≤A)(ht:0≤t)(hh:0 ≤ h)(hV:0≤v)(he:0≤ε)(hD:0≤ D)(hD':0 ≤ D')(hb:0 ≤ b)(hK:0 ≤ θ) : 0 ≤ tributary l k m B K c h v A D D' θ t b ε:=by
    have hx:= mead_pos (m:=l*m) hC; have hr:= warQ (n:=l*k) (m:=l*m) hC; have h1:=zero_lt_one.trans_le hk; have h2:= zero_lt_one.trans_le hC
    unfold tributary Apron.Grove.chipE Apron.Grove.snap Chamber.face Chamber.age whirl blowP expat tumbler; positivity
lemma tributary2 (l k m B:ℕ)(s t C u h h' M D D' θ K b ε:ℝ)(ht:s ≤ t)(hv:0 ≤ b): tributary l k m B s C h h' M D D' θ K b ε ≤ tributary l k m B t C h h' M D D' θ K b ε:=by
    unfold tributary Apron.Grove.chipE; have hx:0 ≤ whirl l B:=by unfold whirl; positivity
    gcongr
end Rift
end -- remove extra paragraph depending header
end YM.MassiveQCD.Rebus
#print axioms YM.MassiveQCD.Rebus.Rift.freightRate
