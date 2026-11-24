import YM.QCD.Purse.Fuel
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Entrance
/-! # Real layer. hue dictionaries on arbitrary virtual-τ labels; convert only via corresponding j Tape. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Shells
open ConnectedActivityE6 ConnectedActivityE6.Blaze Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation
open QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side}{j n l k : ℕ} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {O R : BudgetPoint} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B t t' w y u: ℝ}
variable {δ β B₀:ℝ}{Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T (trimP T R δ β B₀)}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N)
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage
open Ursell QCD.GasP Stained March Graph AnalyticBridge.LocalGaussianLaws
open WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open Spice Lat Multi Multi.Puff Kit Jets Port Fork Sands Fj
variable {N':Libretto su j}
open Garden Stew Dust Brick YM.Next.Free Jets.Touch Orbit Further Leaf Tee Flume Quarry Pine
open Planned.AtomRegular
lemma cin (C:Libretto su j)(Z:Hera.Rights su j)(A:ℝ) : 0 ≤ carryFee C Z A :=by unfold carryFee flareN Jive coreP ott; positivity [patterns_nonneg j,Z.large,Lute.phrase_nn C]
lemma sinR (C: Hera.Rights su j) : 0 ≤ Hera.grandFee C:=by unfold Hera.grandFee; positivity [patterns_nonneg j,C.large]
lemma alert (C:Libretto su j)(O:BudgetPoint) (d:ℕ):0 ≤ Hera.dueFee C O d:=by unfold Hera.dueFee Hera.ripple; positivity [Lute.leading_one C]
-- core cost BEFORE L. flagged extra bucket reserve.Archive after A.Phase
abbrev arid (p:ℝ):= (1+(Malachite.radiusD p:ℝ))^2
def fluteT (P:Libretto su j)(Z:Hera.Rights su j) (I:BudgetPoint)(a:ℝ)(n:ℕ):=2+(1+carryFee P Z a+Hera.grandFee Z)*Hera.dueFee P I n*(1+(n:ℝ))^15
def caseT (P:Libretto su j)(Z:Hera.Rights su j) (I:BudgetPoint)(L:Side)(x:ℝ):=2+ arid x*Hera.grandFee Z*Hera.dueFee P I (deckP L x)
lemma alertF (C:Libretto su j)(Z:Hera.Rights su j) (I:BudgetPoint)(a:ℝ)(n:ℕ): (2+(max (carryFee C Z a) (Hera.grandFee Z))* Hera.dueFee C I n*(1+(n:ℝ))^15) ≤ fluteT C Z I a n∧ 2≤ fluteT C Z I a n:=by
    have hx:= alert C I n; unfold fluteT; have hp:=cin C Z a; have ht:=sinR Z
    refine ⟨add_le_add_right ?_ _, le_add_of_nonneg_right (by positivity)⟩; gcongr; exact max_le (by linarith) (by linarith)
lemma caseN (C:Libretto su j)(Z:Hera.Rights su j) (I:BudgetPoint)(L:Side)(x:ℝ): 2≤ caseT C Z I L x :=by unfold caseT; apply le_add_of_nonneg_right; exact mul_nonneg (mul_nonneg (sq_nonneg _) (sinR Z)) (alert ..)
-- post L Event. Receipt.No failure at any brush.C Fine.C. A ℛ prog paid β^-1/32. singles height. turbulence terms potentially w=β^δ times. pay τa. ops card times β^-e.
open Jets.Sun
structure RoomZ (L:Side)(N:ℕ) (x t h y ξ A w z z':ℝ) : Prop where
   dawn : ∀ τ:ℝ, 0≤τ → τ≤ chip L x→
     ((arid x*(Real.exp τ*τ^2)+A*τ)*|z|+τ*|z'|) ≤ fern L^5*τ∧
     ∀ p:ℝ,0≤p→ p ≤ (geoQ L x N:ℝ) →(arid x*τ*(τ*Real.exp τ + p*(ξ*(w/(t/2))))*|z| +arid x*τ*|z'| ≤ fern L^5*τ)∧ (arid x*(w/(t/2))*|z| ≤ fern L^5)
   swift : arid x*(cashM L h x)⁻¹*|z| ≤1
lemma narrowZ (L:Side): Seat L 0 (fun x=> (Malachite.radiusD x:ℝ)):=by
   unfold Malachite.radiusD; push_cast; simpa using! ((Seat.radius.ponies ((Seat.radius.timesL (4:ℝ)).comb (Seat.numbers 2))|>.above (by linarith)).comb ((Seat.radius (L:=L)).timesL (2:ℝ))) -- cast add
lemma mesa (L:Side): Seat L 0 arid:=by unfold arid; simpa only [zero_mul] using ((Seat.numbers (1:ℝ)).comb (narrowZ L) |>.powered 2)
lemma gridE (L:Side): Seat L 0 (fun x=> (deckP L x:ℝ)):=by unfold deckP paceD; simp only [Nat.cast_pow,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]; simpa only [zero_mul,Malachite.radiusD,Nat.cast_pow,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using! ((((((narrowZ L).comb (Seat.numbers 2)).timesL L.val).timesL (2:ℝ)).comb (Seat.numbers 1)).powered 4)
lemma geog (L:Side)(N:ℕ): Rate su L 0 (fun x=> (geoQ L x N:ℝ)):=by unfold geoQ; simp only [Nat.cast_mul, Nat.cast_ofNat]; exact ((((gridE L|>.timesL (2:ℝ)).times _).times N).timesL _).ruled
lemma pluckZ (L:Side)(N:ℕ)(a h' ξ Y:ℝ) (t u z z':ℝ→ℝ)(hx:0<a)(he:Rate su L (-(1/2)) t)(hy:Rate su L (-(1/32)) u) (hP:Rate su L 0 z)(hG:Rate su L (-(1/2)) z') : ∀ᶠ p in atTop, RoomZ L N p (coneK L a p) h' Y ξ (u p) (t p) (z p) (z' p):=by
    let s i:= |t i|/(coneK L a i/2); let x i:=|z i|; let y i:=|z' i|
    have hv{a':ℝ→ℝ}{ρ}(h: Rate su L ρ a'): Rate su L ρ fun i=>|a' i|:= h.compare (Eventually.of_forall fun i=>(abs_abs _).le)
    have hx':=hv hP; have hy':= hv hG; let qG:ℝ:= -(1/32)
    have hs : Rate su L qG s:=by have hh:= hv he|>.mul (shade_e L hx.ne'); exact ((hh.congr (Eventually.of_forall (fun i=> (div_eq_mul_inv ..).symm))).weaken (by unfold qG; norm_num)) -- check orientation
    have ht:= mesa L|>.ruled; let D i:= arid i; let g i:= geoQ L i N; have hM:=geog L N
    have hm: Rate su L qG (fun i=> (D i*(chip L i*Real.exp 1)+u i)*x i+y i):= (( (( (ht.mul (chip_rate L|>.mul_right _)).weaken (by norm_num[qG])).add hy).mul hx').weaken (by linarith)).add (hy'.weaken (by norm_num[qG]))
    have hU: Rate su L qG (fun i=> D i*(chip L i*Real.exp 1+ g i*(|ξ| *s i))*x i+D i*y i):=(( (ht.mul (((chip_rate L|>.mul_right _).weaken (show -1 ≤ qG by norm_num[qG])).add ((hM.mul (hs.mul_left _)).weaken (by linarith)))).mul hx').weaken (by linarith)).add ((ht.mul hy').weaken (by norm_num[qG]))
    have h : Rate su L qG (fun i=> D i*(s i *x i)):= (ht.mul (hs.mul hx')).weaken (by linarith)
    have hW: Rate su L (-1) (fun i=>D i*(cashM L h' i)⁻¹*x i):=((ht.mul (cash_h L h')).mul hx').weaken (by norm_num)
    have hF :0 < fern L^5:=by positivity [fern_pos L]
    have hJ : qG <0:=by norm_num[qG]
    filter_upwards [hm.below hJ _ hF,hU.below hJ _ hF,h.below hJ _ hF,hW.below (by norm_num) 1 one_pos,event_chip L 0,kentucky L hx] with i h1 h2 h3 h4 h5 h6; constructor; swap
    · exact (le_abs_self _).trans h4
    intro τ hw hτ
    let k:= chip L i; let V:= |t i|; let v:= coneK L a i; have hv':0<v:=mul_pos hx (pow_pos h6.1 _)
    have hq:τ*Real.exp τ ≤ k*Real.exp 1:= mul_le_mul hτ (Real.exp_le_exp.mpr (hτ.trans h5.2.2.1)) (Real.exp_pos _).le h5.2.1.le
    have hD:0 ≤ D i:= sq_nonneg _; have H := abs_nonneg (z i)
    constructor
    · rw [show arid i*(Real.exp τ*τ^2) = D i*(τ*Real.exp τ)*τ by unfold D; ring]; change ((_*_+_)*x i+τ*y i) ≤ _
      rw [← add_mul, show _ +τ*y i = ((D i*(τ*Real.exp τ)+u i)*x i +y i)*τ by ring]
      refine mul_le_mul_of_nonneg_right (le_trans ?_ ((le_abs_self _).trans h1)) hw; gcongr
    intro p hp hx
    have hz : |t i/(coneK L a i/2)|= s i:=by rw [abs_div,abs_of_nonneg (half_pos hv').le]
    have h' : ξ*(t i/(coneK L a i/2)) ≤ |ξ| *s i:=by rw [← hz,← abs_mul]; exact le_abs_self _
    have hy : t i/(coneK L a i/2) ≤ s i:=by rw [←hz]; exact le_abs_self _
    refine ⟨?_,?_⟩
    · change D i* τ*(_+_)* x i + D i*τ*y i≤_
      rw [show _+ _ = ((D i*(τ*Real.exp τ + p*(ξ*(t i/(coneK L a i/2))))*x i+D i*y i)*τ) by ring] -- nested wrong
      apply mul_le_mul_of_nonneg_right _ hw; apply le_trans _ ((le_abs_self _).trans h2)
      have hm:0 ≤ |ξ| *s i:=mul_nonneg (by positivity) (hz ▸ abs_nonneg _); gcongr ?_ * (?_ + ?_) * ?_ + ?_
      calc _ ≤ p*(|ξ| *s i):=mul_le_mul_of_nonneg_left h' hp
           _ ≤ _:=mul_le_mul_of_nonneg_right hx hm
      exact le_rfl
    apply le_trans _ ((le_abs_self _).trans h3); rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hD; exact mul_le_mul_of_nonneg_right hy H
end YM.QCD.Shells
