import YM.Rebus.Ruler
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
-- forecast salary sF,ε etc.
variable {δ q₀ κ₀ σ η u v r r' t d a a' z w w' s C μ:ℝ}
variable {X Y Z Y₀ Y₁:ℝ→ℝ}{Sα :ℝ}
namespace Rift
local notation "g"=>su
lemma pmul (h:Rate su L s X) (he: Rate su L 0 Y):Rate su L s (fun x=> X x * Y x):=by simpa only [add_zero] using h.mul he
lemma pmul' (h:Rate su L s X)(he:Rate su L 0 Y):Rate su L s (fun x=>Y x * X x):=by simpa only [zero_add] using he.mul h
lemma powV (h:Rate su L 0 X)(n:ℕ):Rate su L 0 (fun x=>X x^n):=by simpa only [zero_mul] using h.pow n
lemma abi (h:Rate su L s X): Rate su L s (fun x=>|X x|):= h.compare (by filter_upwards with x; rw [abs_abs])
lemma funds (h:Rate su L (-(1/2)) X)(he: Rate su L (1/2) Y)(v:ℝ) : Rate su L 0 (fun i=>chant (X i) (Y i) v):=by
    unfold chant; have hz:Rate su L (-(1/2)) (fun i=>X i^2):=(h.pow 2).weaken (by norm_num); convert he.mul ((h.mul_left v).add (hz.mul_left v)) using 1; ring
lemma chops (h:Rate su L (-(1/2)) X)(he:Rate su L (1/2) Y)(hp:Rate su L (1/2-1/32) Z)(v:ℝ) : Rate su L (-(1/32)) (fun i=>arcV (X i) (Y i) (Z i) v):=by
    unfold arcV; refine Rate.add ?_ (((he.mul_right v).mul (h.pow 2)).weaken (by norm_num)); convert (h.mul_left v).mul hp using 1; ring
-- fixed AFTER L. Shape CP Shelf purchase exponent.c.Spare gap.
lemma fundsDV {C A:ℝ→ℝ} (h:Rate su L (-(1/2)) X)(h':Rate su L (-(1/2)) Y₀)(hz:Rate su L (-1) C)(he:Rate su L (1/2) Y)(hp:Rate su L (1/2-1/32) Z)(hv:Rate su L (-(1/32)) A)(m n:ℝ): Rate su L (-(1/32)) (fun i=> swapV (X i) (Y₀ i) |C i| (Y i) (Z i) m n (A i)):=by
    have hQ: Rate su L (-1) (fun i=> Y₀ i^2):= by convert h'.pow 2 using 1; norm_num
    exact (he.mul ((hQ.mul_left _).add ((abi hz).mul_left _))|>.weaken (by norm_num)).add (((chops h he hp m).mul_left _).add (pmul hv (funds h he m)))
lemma stocks (L:Side)(N:ℕ):Rate su L 0 (fun i=>stockN N (radiusB i)):=by
    unfold stockN; push_cast
    let X:= Rate.radius_price (G:=su) (L:=L)
    exact (((powV ((((X.add (Rate.const 1)).add X).add (Rate.const 1)).add (Rate.const 1)) 4).mul_left 2).mul_right _).mul_right _
lemma shivery (L:Side)(N:ℕ)(v:ℝ)(m:ℕ)(δ z:ℝ→ℝ)(h:Rate su L (-(1/32)) δ): Rate su L (-(1/32)) (fun i=>Anomaly.shiver m v v (stockN N (radiusB i)*δ i) (δ i)):=by unfold Anomaly.shiver; exact (((pmul' h (stocks L N)).mul_left _).mul_right _|>.add (h.mul_left _)).mul_left _
lemma touch {M₂ v m d cp t φ u w A':ℝ→ℝ} (M M' Vp :ℝ)(hm:1 ≤ M)(hs:M<M')(hV:1 ≤ Vp)(hS:Vp<M') (gT:Hypnos.State su)(S:Patch)(N l t₀:ℕ)(hφ:Rate su L (-(1/2)) φ)(hv: Rate su L (-(1/2)) v)(hCp:Rate su L (-(1/32)) cp)(ht:Rate su L (-(1/32)) t)(hu:Rate su L (-1) u)(hm2:Rate su L (-(1/32)) M₂) (h:Rate su L (1/2) m)(hp:Rate su L (1/2-1/32) d)
 (hw: ∀ᶠ x in atTop,gT.m*φ x ≤ w x∧0 ≤ M₂ x∧1 ≤ A' x ∧ chant (φ x) (m x) gT.web.scale+1≤ A' x ∧ Vp*chant (v x) (m x) gT.web.scale≤ A' x):
 ∃ D₀ D₁ Y:ℝ→ℝ, Rate su L (-(1/32)) D₀ ∧ Rate su L (-(1/32)) D₁ ∧ Rate su L (-(1/32)) Y ∧∀ᶠ x in atTop,Talon S N (radiusB x) l t₀ gT Vp (t x) M (M₂ x) M' (φ x) (v x) (cp x) (m x) (d x) (u x) (D₀ x) (D₁ x) (w x) (Y x) (A' x) :=by
    obtain hD:= fundsDV hv hφ hu h hp ht gT.web.scale Vp; have hs':= (stocks L N); have hx:= shivery L N M' (l*t₀) _ (fun _=>0) hm2
    let P:= AnalyticBridge.LocalGaussianLaws.Current.curlTariff su S 0; have hk:= abi ((hCp.mul_left (P^2)).add ht)
    refine ⟨_,_,_,abi hx,abi hD,hk,?_⟩
    filter_upwards [hw,hk.below (by norm_num) _ (sub_pos.mpr hS), (pmul' hm2 hs').below (by norm_num) _ (sub_pos.mpr hs), hm2.below (by norm_num) _ (sub_pos.mpr hs),hD.below (by norm_num) 1 zero_lt_one] with x h hz hx hy hD
    obtain ⟨h,hx',hv,hM,h'⟩:= h; rw [abs_abs] at hz; refine ⟨hV,hx',hS.le,hs.le,abs_nonneg _, le_abs_self _, (le_sub_iff_add_le).mp hz,(le_sub_iff_add_le').mp ((le_abs_self _).trans hx),(le_sub_iff_add_le').mp ((le_abs_self _).trans hy),h,hv, (add_le_add_right ((le_abs_self _).trans hD) _).trans hM,h',le_abs_self _,le_abs_self _,abs_nonneg _,abs_nonneg _⟩
end Rift
end
end YM.MassiveQCD.Rebus
#print axioms YM.MassiveQCD.Rebus.Rift.touch
