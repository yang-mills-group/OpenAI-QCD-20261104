import YM.QCD.Loom.Loom
/-! # output address step including operator scopes. Per-meristemity later. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Creek
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden Footprint Bay Run Jets.Sun Pine Grass
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f:Side}{P:Teller su}{δ β b τ μ W C:ℝ}{Q:Target su P}{o :Target.Order su W}{R:BudgetPoint}{N m l i j k:ℕ}
variable {η p h z a a' t v V u u' q:ℝ} {K J:Type}[Countable K][Countable J]
variable (L:Flight j k)(d:f.val=c.val*L.L.val)(O:KernelChoices)
variable {T : Tube su (Flight.visit L O d)} {W' :ℕ→Atom su 2} {P':Plan k}
variable {X : St f}
local notation "S"=> Flight.visit L O d
local notation "PI"=> trimP T R δ β b
variable (p:Rise f N J K)(H:Cash W τ μ L.L Q o C T (trimP T R δ β b)) (G:Sun L c f d η h z a a' m X) (V':Swathe L d X W' P' h η a u v i)
local notation "R'"=> radiusB τ
local notation "Z"=> G.equip N (radiusB τ)
local notation "U"=> roof (Z) p 30 R'
variable (Γ: Land c (Site c) (Site c)){Y: Pays c (Site c) (Site c)}
set_option quotPrecheck false
-- status of each mark EBIT. must not assert guilt posterior derivative uniqueness.
def Within (θ a:ℝ)(F:Tree.Forest (Flight.visit L O d).ratio)(Γ₀:Land c (Site c) (Site c)) :Prop:=
    let Y:= (tableau L d O p H G V' Γ₀); let P:= Y.suitcase F
    let b:= unitsP Q L.L μ (PI).beta τ C (shiftCost L.L τ (romp L.L)) (demandQ L.L θ τ)
    Y.Famous ∧ Y.gator ∧ (∃ w, (P.Depth b w 0) ∧ (∀ ZS:Coat T F,ZS.x=τ → ZS.width=o.K →∀ v, ‖token c N a (P.shootsP ZS v)‖ ≤∏ i∈v,P.dues b w i) ∧ (∀ m k r:ℕ,∀ x:ℝ,Ac.Hit P.full R' (fun v=>P.titleP b w 0 v m k r x) b.exponent (b.ceiling m r k x))) ∧ ∀ ZS:Coat T F,ZS.x=τ→ ZS.width=o.K →
      HasSum (fun i=> (X 1).det^N • (Cove.light _ (Matter.overhead ZS (PI) Q.table • P.drawP ZS i)*gauss (Lat.copies N (wood P' 0 L.land ZS.V)))) ((S).push β (Emitter L d O p T δ β (PI).v R W' X) ZS.V)
include H in
lemma haken (hd:0<δ): GaugeInvariant (trimP T R δ β b).exponent:=by
   have hi: GaugeInvariant (PI).eval:= Presented.lawful_gi H.laws.intake.cap
   intro k UX; have ht:= hi k UX; unfold Rep.eval at ht; simp only [trimP,hardy,gauge_flags] at ht; exact Real.exp_injective (mul_right_cancel₀ (by positivity) ht)
lemma ray (F:Tree.Forest (Flight.visit L O d).ratio) {θ ζ w₁ w₂:ℝ}(hr:0<w₁)(hh:River L d O p H G V' F θ ζ Γ Y w₁ w₂ q l)(hp:p.Wave R.threshold)(hd:0<δ)(hv:0<η)(hB:0 < radiusB τ):Within L d O p H G V' θ ζ F Γ:=by
   let X':= tableau L d O p H G V' Γ
   have he:X'.Famous:=hh.1; let P':= X'.suitcase F
   obtain ⟨p₁,hk,hp₁,hζ,hpc,hQ,hL⟩:=hh.2.1
   have ht: Cove.Count Z p U:= (roofs Z p 30 R' le_rfl hB).1
   refine ⟨he, ?_, ⟨p₁,hk,?_,fun m k r x=> P'.priceP hk m k r x⟩,fun X hu hw=>Loom.crop L d O p H G V' Γ F he X hu hw hh.2.2 ht hp hd (haken L d O H hd) (hpc X.V) hQ (sizeA P' hp₁ hk X (Fleet.forwarded _ _ he) hu hw hζ fun v=> arena P' (shiftCost L.L τ (romp L.L)) (demandQ L.L θ τ) _ hL (Fleet.forwarded F X' he) X v hu hw)⟩
   · refine entwine _ _ ?_ (entwine _ _ (Fleet.branch H V' hv rfl) (sailed H hh.2.2 hr))
     exact Fleet.huesL _ _ _ hp ht
   intro X₁ he₁ hu₁ v; exact arena P' (shiftCost L.L τ (romp L.L)) (demandQ L.L θ τ) _ hL (Fleet.forwarded F X' he) X₁ v he₁ hu₁
end YM.QCD.Loom
