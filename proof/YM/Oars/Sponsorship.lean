import YM.Oars.Mother
import YM.Oars.Summer
import YM.Oars.Pigments
import YM.Oars.Prelude
/-!
 # Local booths in actual clock line.Earn.Frame scaling Verity
-/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Sail
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
variable {c f L:Side}{β τ :ℝ}
variable {I E J G Gv:Type}[Fintype I][Fintype J]
open Sail Kites Plate.Card QCD.Calm Acre Rails.Reference Rails
open QCD.Acre.Rails.Bank QCD.Acre.Rails.Bank.Hike Stags
open MassiveQCD.Twist
local notation "iC"=> (42/256:ℝ)
local notation "i₀"=> (46/256:ℝ)
local notation "k₀"=> (1/256:ℝ)
local notation "W₀"=> (1/8:ℝ)
local notation "Ω₀"=> (3/16+1:ℝ)
variable (L:Side)
local notation "s₀"=> Kit.slope L
local notation "Ω₁"=> (3/16+1:ℝ)
-- exponent pre/post control.Tensor
noncomputable def barren (θ M A B N:ℝ)(i l k n H D d:ℕ)(y:ℝ):=M* Real.exp ((1/16:ℝ)*81)* B * (roomAt L θ y * N) + ((Kit.slope L^(d+1)*M)*(roomAt L θ y*N)+ArchC L θ H i k n l D y)
-- remove A. Harvest input inventory HV ≤1.M.Expr shape exact.Pilot.D parameters.D,n.
structure Monthly (L:Side)(i Fo Bo H M n Dx Dl d:ℕ)(θ A B Mξ C D K y:ℝ) :Prop where
    high :  0 <roomAt L θ (run L y)
    warm : 0 < roomAt L θ y
    together : roomAt L θ (run L y) ≤4*roomAt L θ y ∧ roomAt L θ y ≤4* roomAt L θ (run L y)
    mark : bonus Fo (highR L (run L y)) (1/32)*(roomAt L θ (run L y) * (Real.exp (W₀*81)*B*K + K))+roomAt L θ (run L y) ≤ spareCut (Jets.Touch.chip L (run L y)) -- K
    flag : let V:=run L y; (taxK L V ((2-1)/2))⁻¹ ≤ spareCut 1 -- field.costT ratio.Signal.
    rebater: tallyUp L i M n y ≤ roomAt L θ y
    allowance : DeckT L Fo y (Bo*C)
    rights : Bo*C ≤ Real.exp ((W₀/128)*radiusB (run L y))
    stock : let V:=run L y; ∃ K0:ℝ, 0 ≤ K0 ∧ pTag L i M n V*D+B*(A*(D*(barren L θ Mξ A B K i Dx M n H Dl d V)))≤ K0 ∧ bonus Fo (radiusB V) k₀*K0 ≤1 ∧ 0≤barren L θ Mξ A B K i Dx M n H Dl d V ∧ 0 ≤ pTag L i M n V
    -- off costs with error slack caller set.M weighting.Shuffle.
 
lemma collects (i Fo Bo H M n Dx Dl d:ℕ)(θ A B Mξ C D K:ℝ)(ht:0<θ)(hA:1≤A)(hB:1≤B)(hZ:0≤Mξ)(hp:0≤C)(he:0≤D)(hK:0≤K):∀ᶠ x in atTop, Monthly L i Fo Bo H M n Dx Dl d θ A B Mξ C D K x:=by
    let u:=Mξ*Real.exp ((1/16:ℝ)*81)*B*K + ((Kit.slope L^(d+1)*Mξ)*K+1); have hv:0≤u:=by unfold u; have ht:=hB; positivity [Kit.slope_pos L]
    let Q:= u; let V:= roomAt L θ; let Z:=barren L θ Mξ A B K i Dx M n H Dl d; have hxW:= convoy L Fo (fun _=>(Bo:ℝ)*C) 0 (Rate.const _); have hw : ∀ᶠ x in atTop,(Bo*C:ℝ)≤ Real.exp ((W₀/128)*radiusB x):=by
        apply (Reel.playability L (a:=W₀) 0 (fun _=>Bo*C) (by norm_num) (Rate.const _)).mono; intro i hi; exact (le_abs_self _).trans hi
    have hU:0≤B*A*D*Q:=(by positivity); have hg:= loot L θ Fo i M n D (B*A*D*Q) ht he hU -- arg order tS.
    let f:=fun i:ℝ=> (taxK L i ((2-1)/2))⁻¹; have hh: Rate su L (-1) f:= couplings L (by norm_num : (0:ℝ)<(2-1)/2)
    let w:=W₀; have hα:0<spareCut 1:=by unfold spareCut; rw [mul_one,sub_pos]; exact Real.exp_lt_one_iff.mpr (by norm_num)
    have hS:= Work.E09.betaF_growth su L
    filter_upwards [hS.eventually (harvestIn L θ (Real.exp (W₀*81)*B*K+K) ht Fo (by positivity)),hS.eventually (hh.below (by norm_num) (spareCut 1) hα), shuttle L θ,hS.eventually (shuttle L θ),subsid L θ i M n,hxW,hS.eventually hw,hS.eventually hg,hS.eventually (reliefStage L θ H i M n Dx Dl 1 zero_lt_one ht),hS.eventually (event_chip L 1)] with x hY hV hR heQ hh' ht' hH h hp hD; let q':=run L x
    have hk:0≤ Z q':=by
         unfold Z barren ArchC; have hX:=heQ.1; change 0≤ Mξ*_ *B*(V q'*K)+ ( (Kit.slope L^(d+1)*Mξ)*(V q'*K)+_); unfold FeeE Girdle.price MassiveQCD.Lyre.Drawing.crownCost -- hΦ + ψ terms.Flow.N.
         let s:=V q'; have hS:0<s:=heQ.1; have hJ:=hD.1
         unfold Reel.voiceE Girdle.tariff Girdle.shift King.flowM King.jelly QCD.Shells.Warmlet.chill; positivity [(hD.1),hD.2.1,Kit.slope_pos L, fan_pos L (-θ/4) q', show 0 ≤ V q' from heQ.1.le,show 0 ≤ Jets.Touch.chip L q' from hD.2.1.le]
    let f:=pTag L i M n q'; have hf:0 ≤ f:=by unfold f pTag FeeE; unfold Reel.voiceE Girdle.tariff Girdle.shift King.flowM; positivity [hD.1]
    have hp':Z q' ≤ Q* (V q'):=by unfold Z barren; apply (add_le_add_right (add_le_add_right (show ArchC L θ H i M n Dx Dl q' ≤ _ from hp) _) _).trans_eq; unfold Q u; unfold V q'; ring -- order
    let a:= f*D+B*(A*(D*Z q')); have hA0:0 ≤ a:=by unfold a; positivity ; -- positivity.Keep.
    have hhK:0 ≤ bonus Fo (radiusB q') k₀:=by unfold bonus Footprint.payment Footprint.degreeIncome; exact mul_nonneg (by positivity) (inv_nonneg.mpr (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num)))) -- inverse.
    refine ⟨heQ.1,hR.1,⟨hR.2.2,hR.2.1⟩,hY,(le_abs_self _).trans hV,hh',ht',hH,⟨a,hA0,le_rfl,?_,hk,hf⟩⟩
    refine (mul_le_mul_of_nonneg_left (?_ : a ≤ f*D+(B*A*D*Q)*(V q')) hhK).trans h; unfold a; apply add_le_add_right; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp' he) (zero_le_one.trans hA)) (zero_le_one.trans hB)); exact le_of_eq (by ring) -- fix.
end YM.MassiveQCD.Sample.Sail
#print axioms YM.MassiveQCD.Sample.Sail.collects
