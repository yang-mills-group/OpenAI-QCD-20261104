import YM.Cardinal.Wing
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
namespace Drawing
open Massive.Poised QCD.Shells Cupola Plate Card Iris Puff Patron
open Ac QCD.Cove.Send Warmlet Push.Local Massive.Poised.Plans Massive.Poised.Plans.Stamp
open Massive.UV
variable {E' K':Type}{q': Bool}
-- Pu.6
variable (Qx:Puff f 6 E' q')(Tq:Film f 6 Unit K')(Oq:Twist.Register P₀ (Puff.roll 6 Qx) Tq)
variable (A A' :Cover) (Qe: Seal 6 (wrap f A) Qx)
local notation "Aᴮ"=>fun (_:Unit)=>wrap f A
set_option quotPrecheck false
local notation "A⁺"=> ((Flight.visit L' K d).ratio.parent ∘ (Aᴮ))
local notation "Tᴮ"=>fun (_:Unit)=>wrap c A'
local notation "K₀"=> topM
local notation "qᴮ"=>fun (_:Unit)=>q'
local notation "Y"=> Twist.result P₀ (Puff.roll 6 Qx) Tq Oq
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
variable (X:Clusters (vantage L' d K H G U Γ (Twist.result P₀ (Puff.roll 6 Qx) Tq Oq) (fun (_:Unit)=>wrap f A) φ).Bright → RegularAddress c)
variable (hM:∀ i,(X i).support= GasP.seatP ((vantage L' d K H G U Γ (Twist.result P₀ (Puff.roll 6 Qx) Tq Oq) (fun _:Unit=>wrap f A) φ).lightF) i)
variable (F':Cash W τ μ L'.L Q o C T (lore (trimP T O δ β b)))
local notation "Cⁱ"=> crude Tx χ X
local notation "a⁺"=>  budAtlas (A⁺) (30*B)
local notation "I✡"=> Reel.Answer 6 (A⁺) (Cⁱ) (χ') Set.univ
local notation "E✡"=> (Reel.render 6 (A⁺) φ t₀ Cⁱ (χ') Set.univ)
local notation "Z✡"=> Reel.speaker (qᴮ) (E✡)
variable (hSup:Supplies L' d K H G U Γ (Twist.result P₀ (Puff.roll 6 Qx) Tq Oq) (fun (_:Unit)=>wrap f A) φ χ (fun _=>q') t θ P₂.order P₂.power)
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
local notation "Uⁱ"=> A⁺ ()
local notation "t✡"=> wrap c A'
include hSup hM hR hp
lemma roomy (i:I✡) : halo (20*B) {wrap c A'}⊆(P✡) i:=by
    refine Subset.trans ?_ (spindle L' d K H G U Γ Qx Tq Oq A φ X hM hSup i); intro x hx; obtain ⟨y,hy,hx⟩:= halo_spec.mp hx; apply halo_spec.mpr
    rw [Finset.mem_singleton.mp hy] at hx; have hp': separation (A⁺ ()) (wrap c A') ≤ 10* B:=hR.trans hp -- notation.
    exact ⟨_,mem_singleton_self _, (separation_triangle _ _ _).trans (show separation (A⁺ ()) t✡+separation t✡ x≤_ from by omega)⟩
local notation "tr"=> towerE L' d K H G U Γ Qx Tq Oq A φ X Qe hM (χ:=χ)
omit hSup hM hR hp
set_option maxRecDepth 5000 in
lemma spool (i:I✡) (K₀' :U₀)(h: i.val= individual K₀'.code) : Reel.speaker (qᴮ) E✡ i= QCD.Kites.engine t₀ (Keys c 6)∘ ((prescription (N:=6) L' d K Aᴮ φ ((Y).markers K₀'.label.val) (qᴮ)) ∘ (Cⁱ).view i.val):=by
   have hx: (Y).markers K₀'.label.val= (E✡).z i:=(name_stamp L' d K H G U Γ Y Aᴮ φ K₀').symm.trans (congr_arg (χ') h.symm)
   let P:= QCD.Kites.engine t₀ (Keys c 6); funext V; let b:=withdraw 6 A⁺ φ ((Cⁱ).view i.val V); let Z (s:Finset Unit):=pluck (Keys c 6) (Ribbon.burst (fun _=>q') s) b; change pluck _ _ (Plate.turn Unit t₀ b)= P (Z _); exact (turned Unit t₀ b _).trans (congr_arg P (congr_arg Z hx.symm))
include hSup hM hR hp
lemma heritage :wrap c A'∈ budAtlas (A⁺) (30*B) () := by
    exact halo_spec.mpr ⟨_,mem_singleton_self _, hR.trans (hp.trans (by omega : 10*radiusB τ ≤ 30*radiusB τ))⟩
lemma locus_area (i:I✡) : wrap c A' ∈(P✡) i:=roomy L' d K H G U Γ Qx Tq Oq A A' φ X hM hSup hR hp i (halo_subset _ _ (mem_singleton_self _))
omit hR hSup hM hp
lemma civilD (i:I✡) (h: ∀ p: Warmlet H S₁ (Z') P₀, i.val≠ individual p.code) : Dated Tx Fury nectarP τ i.val:=by
    let S:=Tx; have he := marks (N:=6) (Tx) D' nectarP (fun z h=>by rcases z with z|z; exact trivial; exact h.ne_empty rfl |>.elim) i.val i.property.2.1
    -- use mintedH proof for ANY Fleet shape.No need κ.*
    by_contra hm; have hQ: crestP (Tx) i.val ≤ 1:=by by_contra! hz; exact hm (Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨hz,he⟩)
    obtain ⟨v,u,hv,hm,hP⟩:= Moss.individualH (Tx) i.val hQ nectarP he; rcases u with u|u; exact h ⟨u,v,hP⟩ hv; exact hm
 where
   marks {ι M:Type}{N:ℕ}[Fintype M](U:Fleet H ι (ample N M))(D:ι→ Finset M)(f:ι→Prop)(ht:∀ i,(D i).Nonempty→f i)(u:Clusters U.Bright)(hp: (swingE N U D u).Nonempty): stand U f u:=by
       obtain ⟨t,hξ⟩:=hp; obtain ⟨j,hV,hj⟩:= mem_biUnion.mp hξ; obtain ⟨k,hk,hh⟩:=mem_biUnion.mp hj; exact ⟨_,_,hk,ht k ⟨t,hh⟩⟩
structure Mantle (F : I✡→ℝ) :Prop where -- includes unused θ unknown.Power.Walk X.
   sight i : Sight ((X i.val).support) t✡ 2 P₂ u₀ (Reel.speaker (qᴮ) (E✡) i) (F i)
   bills : Ac.Hit (Q✡) B F (αe+2) (Girdle.tariff k₁ 2 P₂.power P₂.order*(Reel.voiceE 2 ε (radiusB τ)* King.flowM L'.L τ))
   rights : Ac.Hit (Q✡) B (Reel.choicePay F D✡) (αe+2) (Girdle.tariff k₁ 2 P₂.power P₂.order*(Reel.voiceE 2 ε (radiusB τ)* King.jelly L'.L τ))
-- ↑ movement costs check hR. `
variable (hF:(αe+2)*frostQ Q.halo ≤ ξ+ε) (hv:0<u₀)
local notation "cʳ"=>Girdle.tariff k₁ 2 P₂.power P₂.order
include hM hB he hR hSup hp hv hF
lemma outp (hT: Reckon 6 (A⁺) φ u₀ (qᴮ) Tx χ D' t₀ X Set.univ P₂ ε ξ 2 (fun (_:Unit)=> 1)) : ∃ F:I✡→ℝ, Mantle L' d K H G U Γ Qx Tq Oq A A' φ X F' F (αe:=αe) (k₁:=k₁) (ε:=ε) (P₂:=P₂) (u₀:=u₀) (t₀:=t₀):=by
    obtain ⟨F,hp',hb,hx,hQ⟩:= hT.burs; let g i:= cʳ *F i; have hi(i : I✡) : (E✡).z i= topM:=itt _ (hT.book.stays i); have hT(i:I✡):Sight ((X i.val).support) (A⁺ ()) 2 P₂ u₀ (Z✡ i) (F i):=hp' i () ((hi _).symm ▸ mem_singleton_self _)
    have hΨ : 0 ≤ cʳ:=by unfold Girdle.tariff Girdle.shift; positivity
    have h (f:I✡→ℝ)(r:ℝ)(h:Ac.Hit (P✡) (radiusB τ) f (ξ+ε) r)(ht:∀ i,0≤f i): Ac.Hit (Q✡) (radiusB τ) (fun i => cʳ*f i) (αe+2) (cʳ*r):=by
        apply Iris.spend_collect; refine budget_mono (budget_scale hΨ (hit_collect t✡ P✡ f (locus_area L' d K H G U Γ Qx Tq Oq A A' φ X hM hSup hR hp) h)) (fun i=>mul_nonneg (mul_nonneg hΨ (ht i)) (Real.exp_pos _).le) ?_; intro i
        let X₀:= (Q✡) i; let X₁:=(P✡) i; have heR: coverNumber B X₀ ≤ coverNumber B X₁*frostQ Q.halo:= (Corona.cover_mono ((grows L' d K H G U Γ Qx Tq Oq A φ X hM F' _).2) _).trans (touring _ Q.halo _ _ (hB ▸ P₂.B_pos) le_rfl)
        have hx':(coverNumber B X₀:ℝ) ≤(frostQ Q.halo:ℝ)*coverNumber B X₁:=by rw [mul_comm]; exact_mod_cast heR
        rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hΨ; apply mul_le_mul_of_nonneg_left _ (ht _); exact Real.exp_monotone ((mul_le_mul_of_nonneg_left hx' (by linarith only [he])).trans ((mul_assoc ..|>.symm.le).trans (mul_le_mul_of_nonneg_right hF (Nat.cast_nonneg _)))) -- cost.Lint
    let t:I✡→ℝ:=Reel.choicePay F D✡; have ht(i):0 ≤ F i:= (hT i).travels
    refine ⟨g,⟨fun i=> Girdle.moving (t:=u₀) hR _ (hT i) hv,h F _ hb ht,?_⟩⟩ -- args hM F order
    have he': Reel.choicePay g D✡=fun i=> cʳ*t i:=funext fun i=> by change Reel.choicePay (fun i=> cʳ *F i) _ _ = cʳ* Reel.choicePay ..; unfold Reel.choicePay; split; rfl; rw [mul_zero]
    rw [he']; exact h t _ hx fun i=> ite_nonneg (ht i) le_rfl -- t choicePay reducible
end Drawing
end YM.MassiveQCD.Lyre
#print axioms YM.MassiveQCD.Lyre.Drawing.outp
