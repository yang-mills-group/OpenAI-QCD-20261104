import YM.Cardinal.Ficus
import YM.Oars.Lavender
import YM.Oars.CowlL
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
abbrev warmA (i:I✡) : Prop:= ∃ j: U₀, i.val=individual j.code ∧ Small H S₁ (Z') P₀ j F'
local notation "κ'"=> warmA L' d K H G U Γ Qx Tq Oq A φ X F'
local notation "ξχ" => Girdle.tariff k₁ 2 P₂.power P₂.order* Reel.voiceE 2 ε (radiusB τ)
local notation "Φ"=>ξχ*flowM L'.L τ
local notation "Ψ"=>ξχ*jelly L'.L τ
local notation "D⁻"=> (radiusB τ:ℝ) /frostQ Q.halo
local notation "Δ"=> chill Q.halo τ
-- Out of Small
lemma tame (i:I✡) (p:U₀)(he:i.val= individual p.code): (Q✡) i=(trunkP H S₁ (Z') P₀ F' p).support:=(congr_arg (Iⁱ) he).trans (stride L' d K H G U Γ Qx Tq Oq A φ X F' p)
include hM
lemma foreign (i:I✡)(p:U₀)(he:i.val= individual p.code) : (P✡) i=past H S₁ (Z') P₀ p:= Eq.trans (congr_arg (fun i=> (X i).support) he) (plumed L' d K H G U Γ Qx Tq Oq A φ X hM p)
omit hM
include hSup hM hR hp hB
variable (hF:0<u₀)
include hF
set_option maxHeartbeats 680000 in
lemma outward (Dx nL:ℕ) (g:I✡→ℝ)(h: Mantle L' d K H G U Γ Qx Tq Oq A A' φ X F' g (αe:=αe) (k₁:=k₁) (ε:=ε) (P₂:=P₂) (u₀:=u₀) (t₀:=t₀)) : ∃ F:I✡→ℝ,
   Ac.Hit (Q✡) B F αe (Reel.voiceE (Dx*nL) 1 (radiusB τ)*(Δ*Φ+Ψ)) ∧ ∀ i, ¬(κ' i) → Flame (Z✡ i) P₂ ((Q✡) i) (wrap c A') u₀ Dx nL (F i):=by
     let Z:= I✡; let b₀(i:Z):=(Q✡) i; let c₀(i:Z):=coverNumber B (b₀ i);
     let q:=(D✡); let r (i:Z):= if κ' i then 0 else g i; let z(i:Z):Prop:= ¬κ' i; have hA i := (locus_area L' d K H G U Γ Qx Tq Oq A A' φ X hM hSup hR hp (χ:=χ) i); have hs(i:Z): t✡∈ b₀ i:= (grows L' d K H G U Γ Qx Tq Oq A φ X hM F' _).1 (hA i); have hV:= hit_collect t✡ b₀ g hs h.bills; have hΩ:= hit_collect t✡ b₀ (Reel.choicePay g q) hs h.rights
     have ht'(i:Z):¬q i→ z i→ B ≤ c₀ i * frostQ Q.halo:=by
           intro hi hh
           by_contra hm; apply hi; apply civilD ; intro p ht; -- equality of affiliation
           have hp : ¬ Small H S₁ (Z') P₀ p F':=fun hl=> hh ⟨p,ht,hl⟩; have hb:= brew H S₁ (Z') P₀ F' p hp (hB ▸ P₂.B_pos); let Y':=past H S₁ (Z') P₀ p; have he:Y'⊆b₀ i:= le_trans (le_of_eq (show past H S₁ _ _ p= (X i.val).support from (foreign L' d K H G U Γ Qx Tq Oq A φ X hM i p ht).symm)) (grows L' d K H G U Γ Qx Tq Oq A φ X hM F' _).1 -- covariance cast
           apply hm; apply le_trans _ (Nat.mul_le_mul_right _ (Corona.cover_mono he B)); exact_mod_cast hb
     let w i:=r i*Real.exp ((αe+1)*c₀ i); let C':= Δ*Φ+Ψ; have hδ:0≤ Δ:= (Real.exp_pos _).le; have hN(i:Z):0≤g i:= (h.sight i).travels; have hr(i):0≤r i:=by unfold r; split; exact le_rfl; exact hN i
     have hr':SumBudget w C':= by
        have hc:= budget_plus (budget_scale hδ hV) hΩ; unfold C' -- differs additive
        rw [mul_assoc (_:ℝ) (Reel.voiceE 2 ε (radiusB τ)) _,mul_assoc (Girdle.tariff ..) (Reel.voiceE 2 ε (radiusB τ)) _]; refine budget_mono hc (g:=w) (fun i=> mul_nonneg (hr i) (Real.exp_pos _).le) ?_
        intro i; change r i*_ ≤ Δ*_ + Reel.choicePay _ _ _ *_; by_cases hv:z i; swap; · rw [show r i=0 from if_pos (not_not.mp hv),zero_mul]; exact hc.1 _
        rw [show r i=g i from if_neg hv]; by_cases hb:q i
        · rw [show Reel.choicePay g q i=g i from if_pos hb]; apply le_trans _ (le_add_of_nonneg_left (mul_nonneg hδ (mul_nonneg (hN i) (Real.exp_pos _).le))); gcongr <;> first|linarith|apply hN
        rw [show Reel.choicePay g q i=0 from if_neg hb,zero_mul, add_zero]; 
        let V:=g i; change V*_≤ Δ*(V*_); rw [mul_left_comm]; apply mul_le_mul_of_nonneg_left _ (hN i); unfold chill; rw [← Real.exp_add]; apply Real.exp_monotone; have ht:0<(frostQ Q.halo:ℝ):=by unfold frostQ; positivity
        have hg:(radiusB τ:ℝ)/frostQ Q.halo ≤ c₀ i:= (div_le_iff₀ ht).mpr (by exact_mod_cast ht' i hb hv); rw [div_eq_mul_inv] at hg; change _ ≤ _+(αe+2)*↑(c₀ i); linarith only [hg]
     let ZV:=Reel.voiceE (Dx*nL) 1 (radiusB τ); let m' i:= ((1+(wag (b₀ i) B:ℝ))^(Dx*nL)*r i); have hu:0 ≤ ZV:=by unfold ZV Reel.voiceE; positivity
     refine ⟨m', Iris.spend_collect b₀ m' (budget_mono (budget_scale hu hr') (fun i=>mul_nonneg (mul_nonneg (by positivity) (hr i)) (Real.exp_pos _).le) fun i=> ?_),fun i hi=>?_⟩
     · exact (mul_comm ..).le.trans (Reel.fresh_bill (b₀ i) (Dx*nL) _ zero_lt_one (hr i))
     have hg:= (h.sight i); have hX:= grows L' d K H G U Γ Qx Tq Oq A φ X hM F' i.val -- U rebound. Need rename let. 
     unfold m'; rw [pow_mul, show r i = g i from if_neg hi]; exact Facets.extended (Counting.Terrain.shelf_out hX.1 hg) (fun j hj=> Corona.extent (b₀ i) B hj (hs i)) hF Dx nL
end Drawing.Claro
end YM.MassiveQCD.Lyre
#print axioms YM.MassiveQCD.Lyre.Drawing.Claro.outward
