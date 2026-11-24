import YM.Cardinal.Ficus
import YM.Oars.Lavender
import YM.Oars.CelsiusL
import YM.Cardinal.Wand
/-! # Bridge Cupola and Siege.Tower: paid on ONE trajectory -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Lyre
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}
variable {j k m i k₁ n:ℕ}
variable {z η p h a a' v δ b s u q:ℝ}{P' : Plan k}{X:Run.St f}
variable (L':Flight j k)(d:f.val=c.val*L'.L.val)(K:KernelChoices)
local notation "S'"=> Flight.visit L' K d
variable {T:Tube su (Flight.visit L' K d)}{W' :ℕ→Atom su 2}
variable (H:Cash W τ μ L'.L Q o C T (trimP T O δ β b))
variable {P₀:Rise f 6 E J} [Countable E][Countable J]
variable {P₁:Plan j}{a₀ b₀ a₁ b₁ w mm :ℝ}{E₁:Offer 1 a₀ a₁}{E₂:Offer 2 b₀ b₁}
local notation "Xγ"=> (pesto P₁ L' d (trunkM E₁ E₂ w mm f))
variable (G:Sun L' c f d η h z a a' m (pesto P₁ L' d (trunkM E₁ E₂ w mm f))) (U :Swathe L' d (pesto P₁ L' d (trunkM E₁ E₂ w mm f)) W' P' h η a u v i)
variable (Γ:Land c (Site c) (Site c)){D':Pays c (Site c) (Site c)}
namespace Drawing.Claro
open Massive.Poised QCD.Shells Cupola Plate Card Iris Puff Patron
open Ac QCD.Cove.Send Warmlet Push.Local Massive.Poised.Plans Massive.Poised.Plans.Stamp
open Massive.UV
variable {E' K':Type}{q': Bool}
-- Pu.6
variable {IE Gp:Type} [Fintype IE]
variable (Qx:Puff f 6 E' q')(Tq:Film f 6 IE K')(Oq: Charter (Gp:=Gp) P₀ Qx Tq)
variable (A A' :Cover) (Qe: Seal 6 (wrap f A) Qx)
local notation "Aᴮ"=>Oq.loc A
set_option quotPrecheck false
local notation "A⁺"=> ((Flight.visit L' K d).ratio.parent ∘ (Aᴮ))
local notation "Tᴮ"=>fun (_:Unit)=>wrap c A'
local notation "K₀"=> ({Oq.K0}:Finset IE)
local notation "qᴮ"=>Oq.style
local notation "Y"=> Oq.V
variable (φ:ℝ)
local notation "B"=>radiusB τ
local notation "Z'"=> G.equip 6 (radiusB τ)
local notation "Zⁱ"=>QCD.Jets.Touch.roof (G.equip 6 (radiusB τ)) P₀ 30 B
local notation "S₁"=>united (VarnC H U 6) (sailP H Γ 6)
local notation "Tx"=> vantage L' d K H G U Γ (Y) (Aᴮ) φ
local notation "U₀"=>Warmlet H S₁ (Z') P₀
local notation "D'"=>Sum.elim (fun u:Wound Zⁱ=> (Y).markers u.val) (fun _: Varn f c⊕Gaze c=>∅)
local notation "χ'"=>swingE 6 Tx D'
set_option quotPrecheck false
open Warmlet MassiveQCD.Lyre Sands
variable {χ:Chi}{α ξ θ t t₀ x x₀ x₁ κ α₁ α₂ ε:ℝ}{P₂: BudgetPoint}
variable (X:Clusters (vantage L' d K H G U Γ (Oq.V) (Oq.loc A) φ).Bright → RegularAddress c)
variable (hM:∀ i,(X i).support= GasP.seatP ((vantage L' d K H G U Γ (Oq.V) (Oq.loc A) φ).lightF) i)
variable (F':Cash W τ μ L'.L Q o C T (lore (trimP T O δ β b)))
local notation "Cⁱ"=> crude Tx χ X
local notation "a⁺"=>  budAtlas (A⁺) (30*B)
local notation "I✡"=> Oq.Role (A⁺) (Cⁱ) (χ')
local notation "E✡"=> (Reel.render 6 (A⁺) φ t₀ Cⁱ (χ') Oq.demand)
local notation "H✡"=> Oq.helm (A⁺) Cⁱ (χ')
local notation "Z✡"=> Reel.speaker (qᴮ) (E✡) ∘ H✡
variable (hSup:Supplies L' d K H G U Γ (Oq.V) (Oq.loc A) φ χ (Oq.style) t θ P₂.order P₂.power)
local notation "kindY"=> (address H S₁ (Z') P₀)
local notation "ι'"=> Clusters (Tx).Bright
-- naming geometry
local notation "Iⁱ"=> aisle L' d K H G U Γ Qx Tq Oq A φ X F'
variable {u₀ u₁ αe:ℝ}{Dx nL r:ℕ}
local notation "Q✡"=> fun i:I✡=>(Iⁱ) i.val
local notation "P✡"=>fun i:I✡=> (X i.val).support
local notation "D✡"=> fun i:I✡=> Dated Tx Fury nectarP τ i.val
variable (hB:P₂.B=radiusB τ)(he:0 ≤ αe)
-- sigma actual, require large compared frost for soft payment. Use a>0 separately
variable (hR:separation ((Flight.visit L' K d).ratio.parent (wrap f A)) (wrap c A') ≤ k₁)(hp:k₁ ≤ 10* radiusB τ)
local notation "Uⁱ"=> A⁺ Oq.K0
local notation "t✡"=> wrap c A'
local notation "tr"=> towerE L' d K H G U Γ Qx Tq Oq A φ X Qe hM (χ:=χ)
open Massive.Poised Massive.Poised.Pipes Massive.Poised.Plans.Girdle
-- A.Call.WhereOut
local notation "κ'"=> warmA L' d K H G U Γ Qx Tq Oq A φ X F'
local notation "ξχ" => Girdle.tariff k₁ 2 P₂.power P₂.order* Reel.voiceE 2 ε (radiusB τ)
local notation "Φ"=>ξχ*flowM L'.L τ
local notation "Ψ"=>ξχ*jelly L'.L τ
local notation "D⁻"=> (radiusB τ:ℝ) /frostQ Q.halo
local notation "Δ"=> chill Q.halo τ
-- Out of Small
variable (hPx:BudgetPoint)(σ:E→ℝ)
-- Tap at registered labels. Range equivalence.W.
lemma tapis (i:E'): Elevator.tap (q:=qᴮ) P₀ (Y) (Oq.ear i)=Qx.fill i :=by
   have ht:=Twist.figures P₀ _ _ Oq.rd (Oq.parts i); unfold Elevator.tap; have h1:(Y).main (Oq.ear i)=Oq.P.mark (Oq.parts i):=ht.1; have h2:(Y).spine (Oq.ear i)=Oq.P.z (Oq.parts i):=ht.2; rw [h1,h2]; exact Oq.source i
include hB hM hp hR hSup Qe
variable (hx: u₀ * t₀ ≤ φ)(hv:0<t₀)(hU:0<u₀)
local notation "ww"=> wiCost (radiusB τ)
variable (hNP:∀ i:E', Sight (Qx.addr i).support (wrap f A) 2 hPx x₁ (Qx.fill i) (σ (Oq.ear i))) -- K.S mandatory.N.B Macro adept
include hx hU hv hNP
local notation "η'"=>Girdle.price ww P₂.power P₂.order Dx nL*crownCost Dx nL (radiusB τ)
-- warrant from Patrol. outputs only pay selected. Geom. errors result
set_option maxHeartbeats 540000 in
lemma nearWard (h: Patrol (O₁:=hPx) L' d K H G U Γ Y Aᴮ φ F' χ P₂ x₁ αe κ qᴮ σ) : ∃ F:I✡ → ℝ, Ac.Hit Q✡ (radiusB τ) F αe (η'*κ) ∧ ∀ i:I✡,κ' i → i∉ Set.range tr→ Flame (Z✡ i) P₂ ((Q✡) i) t✡ u₀ Dx nL (F i) :=by
   let Z:= I✡; obtain ⟨g,hg,h⟩:= h.earn
   let k:Finset I✡:= ∅
   let R i:= trunkP H S₁ (Z') P₀ F' i; let W:= warmA L' d K H G U Γ Qx Tq Oq A φ X F' (χ:=χ); let v(i:Z):Prop:= W i∧ i∉Set.range tr
   have ht(i:{x:Z//v x}) : ∃ j:U₀,i.val.val=individual j.code∧ Warmlet.Small H S₁ (Z') P₀ j F':= i.property.1
   choose t ht hQ using ht -- choose dependent
   have hτ: Function.Injective t:=by
       intro a b h; let l(i:U₀):ι':= individual i.code; exact Subtype.ext (Subtype.ext ((ht a).trans ((congr_arg l h).trans (ht b).symm)))
   have hgX (i:{x:Z//v x}): (Q✡) i.val=(R (t i)).support:= tame L' d K H G U Γ Qx Tq Oq A φ X F' i.val (t i) (ht i)
   have hΘ(i:{x:Z//v x}): t✡∈(R (t i)).support:=by
       have hs:= locus_area L' d K H G U Γ Qx Tq Oq A A' φ X hM hSup hR hp i.val; have hv: t✡∈(Q✡) i.val :=(grows L' d K H G U Γ Qx Tq Oq A φ X hM F' _).1 hs; rwa [hgX] at hv
   let f:Z→ℝ:=fun i=> if h:v i then η'* g (t ⟨i,h⟩) else 0
   have he:0 ≤ η':=by unfold Girdle.price Girdle.tariff crownCost Girdle.shift; positivity
   refine ⟨f,fun x=>?_,fun i hi hX=>?_⟩
   · have hg':= budget_pull t hτ (budget_scale he (hg x)); let z'(i:{x:Z//v x}):= η'* (if x∈(R (t i)).support then g (t i)*Real.exp (αe*coverNumber B (R (t i)).support) else 0); refine Warmlet.walk v z' _ ?_ ?_ (show SumBudget z' _ from hg')
     · intro i hp; unfold f; rw [dif_neg hp]; split; rw [zero_mul]; rfl
     intro i; unfold z'; dsimp only; -- simp f at membership
     split; next hs=> rw [if_pos (show x ∈ _ from (show x∈ (R (t i)).support from (hgX i) ▸ hs)), ← hgX, show f _ = _ from (dif_pos i.property)]; exact mul_assoc .. -- `show f _` incomplete
     next hs => rw [if_neg (fun hx=> hs (Eq.symm (show (Iⁱ) i.val.val=(R (t i)).support from hgX i) ▸ hx)),mul_zero]
   let y:{x:Z//v x}:=⟨i,hi,hX⟩; let Z₀:=t y; have hy:=ht y; have hY:=hQ y; let f' := Z₀.label; let p':= perch H S₁ (Z') P₀ F' Z₀; have hE: (R (t y))=p':= if_pos hY -- trunk if? if not dif
   have hx' : (Y).markers Z₀.label.val=χ' i.val:=(name_stamp L' d K H G U Γ Y Aᴮ φ Z₀).symm.trans (congr_arg (χ') hy.symm); have hT: ((Y).markers Z₀.label.val).Nonempty:=Eq.mp (congr_arg Finset.Nonempty hx'.symm) ((H✡ i).2.2.1)
   let Uv:Grid c→Fields c 6:= (prescription L' d K Aᴮ φ ((Y).markers Z₀.label.val) qᴮ) ∘ (Cⁱ).view i.val; have hP:= h Z₀ X hM hT hY (fun e hE=>?_ ) (fun h=> hX (tower_out L' d K H G U Γ Qx Tq Oq A Qe φ X hM _ Z₀ hy h)); swap -- Ua edit
   · obtain ⟨z,rfl⟩ := spar L' d K H G U Γ Qx Tq Oq A Qe φ X hM _ (hx'.trans i.property.1) e hE
     rw [tapis Qx Tq Oq z,Oq.homeP]; exact (Qe.anchor z).symm ▸ hNP z
   have hξ : Sight p'.support p'.site 2 P₂ φ Uv (g (t y)):= (congrArg (fun X:ι'=> Sight p'.support p'.site 2 P₂ φ ((prescription (N:=6) L' d K Aᴮ φ ((Y).markers Z₀.label.val) qᴮ) ∘ ((Cⁱ).view X)) (g Z₀)) hy).symm ▸ hP -- ▸ direction? equality Q= Q'; `hy` has J typed
   have htV(i j:Site c)(hi:i∈p'.support)(hj:j∈p'.support):separation i j ≤ wiCost B:= (Corona.extent p'.support B hi hj).trans (by unfold wiCost; gcongr)
   have hF:= (hE ▸ hΘ y: t✡∈p'.support); let Λ:= (g Z₀); have hp':0<φ:=zero_lt_one.trans_le hSup.strength; have hΔ:=(Facets.extended hξ (fun i hi=>htV i p'.site hi p'.anchor) hp' Dx nL); have hpY : Flame (Z✡ i) P₂ p'.support p'.site u₀ Dx nL (crownCost Dx nL (radiusB τ)* Λ):= by rw [spool L' d K H G U Γ Qx Tq Oq A φ X i Z₀ hy]; exact Girdle.orbitG Uv hp' hΔ hv hU hx
   unfold f; rw [dif_pos (show v i from y.property)]
   have hm: (Q✡) i=p'.support:= (hgX y).trans (congr_arg RegularAddress.support hE); change Flame (Z✡ i) P₂ _ _ u₀ Dx nL (η' * Λ); rw [hm,mul_assoc]; exact Girdle.living (htV _ _ p'.anchor hF) _ hU hpY
end Drawing.Claro
end YM.MassiveQCD.Lyre
#print axioms YM.MassiveQCD.Lyre.Drawing.Claro.nearWard
