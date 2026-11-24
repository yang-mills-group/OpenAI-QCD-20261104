import YM.QCD.Purse.Farm
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
open Run Jets Jets.Sun
open Ac Trees Labels Animals Further.ShellBirth49.Fusing Collide
-- Hit sum tail.N anchored through op degree. no loss W shape. pre-L recruitment flexible with occupations. independent V roof.Data.
lemma OpsCard {σ τ κ:Type}(f:Finset (Fj σ τ κ)): (ops f).card ≤ f.card:=by
    have hh:= congr_arg Finset.card (pinch f); unfold pin at hh; rw [card_disjSum] at hh; omega
lemma booms (m:ℕ): m+1 ≤ 2^m:=by
    induction m with
    | zero=>simp
    | succ n ih=>rw [pow_succ]; omega
lemma tollR (A B:ι→Support c)(p':ℕ)(β:ι→ℝ)(Q:ℝ)(hx:Ready A p' β t v 1 r)(hk:2*r<1): Ready A p' (fun i=>2*β i) t (2*v) 1 (2*r):=by
    refine ⟨mul_pos (by norm_num) hx.1,hx.2.1,?_,hk,fun i=> mul_nonneg (by norm_num) (hx.2.2.2.2.1 _), heights_factor _ _ _ _ hx.2.2.2.2.2 (by intros; rfl) (by norm_num)⟩
    exact (le_of_eq (by unfold degreePrice Trees.stretch; ring)).trans (mul_le_mul_of_nonneg_left hx.2.2.1 (by norm_num : (0:ℝ) ≤2))
variable {E J: Type}[Countable E][Countable J]{σ:Type}
-- Old foot external censor ok regardless local vs all Ank.
variable {Z W':Fj σ E J→Support c}{w':Fj σ E J→ℝ}{ξ τ x ρ:ℝ}(Q':ℝ)
lemma bold (hp:Ready Z n w' a τ 1 r)(he:2*r<1)(ht:0≤a)(hx:0<ξ)(hg:0≤ρ)(hh:∀ i,W' i⊆ Z i) (Q₀: Finset (Fj σ E J)→Support c) (x:Site c)(hz:∀ i, Q₀ i⊆ i.biUnion Z):
    SumBudget (fun i:Finset (Fj σ E J)=>if 2 ≤ i.card ∧ x∈ Q₀ i ∧ Collide.spark W' i then (ξ⁻¹ * (∏ j∈i,w' j) * (ρ*((ops i).card+1:ℝ)))* currency n a (Q₀ i) else 0) ((ρ*ξ⁻¹)*(2*τ*(2*r)^1*(1-2*r)⁻¹)):=by
   let G j:=2*w' j; have h:=tollR Z W' n _ 0 hp he; have hv:=touch_tail Z n h x 1; have heQ: 0 ≤ ρ*ξ⁻¹:=by positivity
   refine budget_mono (budget_scale heQ hv) (fun i=>?_) ?_
   · split; · have H':0≤∏ j∈i,w' j:= prod_nonneg fun j _=> hp.2.2.2.2.1 j; exact mul_nonneg (by positivity) (Real.exp_pos _).le
     exact le_rfl
   intro i; split
   next ht'=>
    have hs:1 ≤ i.card-1:=by omega
    have hM: Ac.Spark Z i := spark_ac W' Z ht'.2.2 (fun _ _ _ _ ⟨x,u,v⟩=> ⟨x,hh _ u, hh _ v⟩)
    have hU:= hz i ht'.2.1; rw [if_pos hs,touches,if_pos ⟨hM,hU⟩]
    have hg' : (↑(ops i).card+1:ℝ) ≤ 2^i.card:= by exact_mod_cast ((Nat.add_le_add_right (OpsCard i) 1).trans (booms _))
    let p:ℝ:=∏ j∈i,w' j; have hW:0 ≤ p:=prod_nonneg fun j _=>hp.2.2.2.2.1 _
    rw [prod_mul_distrib,prod_mul_distrib, prod_const, ← mul_assoc (ρ*ξ⁻¹)]
    apply mul_le_mul
    · apply le_trans (b:= ξ⁻¹*p * (ρ * (2:ℝ)^i.card)) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg' hg) (by positivity)) ?_; exact le_of_eq (by unfold p; ring)
    · have he':coverNumber n (Q₀ i)≤∑ j∈i,coverNumber n (Z j):= (Corona.cover_mono (hz i) _).trans (Ac.cover Z n hM); unfold currency; rw [← Real.exp_sum,← mul_sum,← Nat.cast_sum]; exact Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast he') ht)
    · exact (Real.exp_pos _).le
    exact mul_nonneg heQ (mul_nonneg (by positivity) hW)
   next h'=> exact mul_nonneg heQ (hv.1 _)
-- caseFee independent sets; Rate/L planned buys arbitrarily at R widths.
lemma courage (L:Side)(V:Libretto su j)(Z:Hera.Rights su j)(p:ℕ):∃ g:ℝ→ℝ, Seat L 0 g ∧ ∀ (x:ℝ)(I:BudgetPoint), I.power=p→ g x=caseT V Z I L x:=by
   let Y x:= Hera.ripple V 1*(1+(1+(deckP L x:ℝ))^Lute.debited j p); have hp:Seat L 0 Y:=by exact ((Seat.numbers 1).comb ((((Seat.numbers 1).comb (gridE L)).powered _).above (by linarith))|>.timesL _)
   exact ⟨fun x=>2+arid x*Hera.grandFee Z*Y x,(Seat.numbers 2).comb (((mesa L|>.times _).ponies hp).above (by linarith)),fun x I h=> by unfold caseT Hera.dueFee Y; rw [h]⟩
lemma booths (L:Side)(V:Libretto su j)(Z:Hera.Rights su j)(p:ℕ)(θ A:ℝ)(he:0<θ)(hA:0<A):∀ᶠ x in atTop,2*fan L (-θ) x<1∧ ∀ I:BudgetPoint,I.power=p→(caseT V Z I L x*(cashM L θ x)⁻¹)*(2*fan L (-θ-θ/2) x*(2*fan L (-θ) x)^1*(1-2*fan L (-θ) x)⁻¹) ≤ A*chip L x:=by
   obtain ⟨g,hg,h⟩:= courage L V Z p
   let G x:=fan L (-θ-θ/2) x; let d x:=2*fan L (-θ) x; let z x:=fan L θ x; let k x:=g x*z x ^2
   have ht: Seat L (-θ) d:= Seat.keeps.timesL 2; have hf:Seat L (-θ-θ/2) G:=Seat.keeps
   have hv: Seat L (0+θ*(2:ℕ)) k:= hg.ponies (Seat.keeps.powered 2)
   have he':Seat L (-θ/2) (fun x=>k x*(2*G x*d x*2)):= ((hv.ponies (((hf.timesL 2).ponies ht).times 2)).above (by push_cast; linarith))
   filter_upwards [he'.shrinks (by linarith) hA,ht.shrinks (by linarith) (D:=1/2) (by norm_num),Delay.shift_pos su L] with x hx hX hA
   have hz:=le_trans (le_abs_self _) hX; refine ⟨hz.trans_lt (by norm_num),fun I he=>?_⟩
   let c:=Jets.Touch.chip L x; have hV:0<c:=healthy_chip hA; have hZ:0 ≤ g x:=by rw [h _ _ he]; linarith only [caseN V Z I L x]
   have ht':0< z x:=fan_pos ..; rw [←h _ _ he,pow_one,show (cashM L θ x)⁻¹=z x^2*c from ?_]
   · rw [show _ * (_ * _ *(1- _ )⁻¹) = (k x*(2*G x*d x*(1-d x)⁻¹))*c from by unfold k G d; ring]
     apply mul_le_mul_of_nonneg_right _ hV.le; apply le_trans _ ((le_abs_self _).trans hx); have hQ : (1-d x)⁻¹ ≤2:= by rw [inv_le_iff_one_le_mul₀ (show 0<1-d x by linarith)]; linarith
     have he₀:0 ≤ 2*G x*d x:=by unfold G d; positivity [fan_pos L (-θ-θ/2) x,fan_pos L (-θ) x]
     exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ he₀) (by unfold k; positivity)
   unfold cashM Jets.Touch.rust z c; simp [mul_comm]
end YM.QCD.Shells
