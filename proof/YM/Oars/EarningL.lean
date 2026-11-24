import YM.Cardinal.Ficus
import YM.Oars.Lavender
import YM.Oars.BossL
import YM.Cardinal.Harvest
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
variable {z vP p h a a' v δ b s u q:ℝ}{P' : Plan k}{X:Run.St f}
variable (L':Flight j k)(d:f.val=c.val*L'.L.val)(K:KernelChoices)
local notation "S'"=> Flight.visit L' K d
variable {T:Tube su (Flight.visit L' K d)}{W' :ℕ→Atom su 2}
variable (H:Cash W τ μ L'.L Q o C T (trimP T O δ β b))
variable {P₀:Rise f 6 E J} [Countable E][Countable J]
variable {P₁:Plan j}{a₀ b₀ a₁ b₁ mm :ℝ}{E₁:Offer 1 a₀ a₁}{E₂:Offer 2 b₀ b₁}
local notation "Xγ"=> (pesto P₁ L' d (trunkM E₁ E₂ (haloK L'.L τ) mm f))
variable (G:Sun L' c f d (coneK L'.L vP τ) h z a a' m (pesto P₁ L' d (trunkM E₁ E₂ (haloK L'.L τ) mm f))) (U :Swathe L' d (pesto P₁ L' d (trunkM E₁ E₂ (haloK L'.L τ) mm f)) W' P' h (coneK L'.L vP τ) a u v i)
variable (Γ:Land c (Site c) (Site c)){D':Pays c (Site c) (Site c)}
namespace Drawing.Claro
open Massive.Poised QCD.Shells Cupola Plate Card Iris Puff Patron
open Ac QCD.Cove.Send Warmlet Push.Local Massive.Poised.Plans Massive.Poised.Plans.Stamp
open Massive.UV
variable {E' K':Type}{q': Bool}
-- Pu.6
variable (A A' :Cover) {x₀:ℝ} {Gn r :ℕ}{Ua:YM.Source.Hol su} {Va:YM.Massive.Lining.Temper.Collage.Exhibit Ua}{R₁:BudgetPoint}{Xb:Label Gn} (Z: CentreFrame (c:=f) R₁ x₀ Xb q' Va A (r+1) E' K') {IE Nκ Gp:Type} [Fintype IE] (Tρ:Film f 6 IE Nκ)(Oq:Charter (Gp:=Gp) P₀ (ritual Z) Tρ)
variable (Qe: Seal 6 (wrap f A) (ritual Z))
local notation "Qx"=> ritual Z
set_option quotPrecheck false
local notation "Tq"=> Tρ
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
variable {χ:Chi}{α ξ θ t t₀ x x₁ κ α₁ α₂ ε:ℝ}{P₂: BudgetPoint}
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
variable {u₀ u₁ αe:ℝ}{Dx nL:ℕ}
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
variable (Θ:Massive.SourceRead.TaperHol)
variable (F₁:Cash W τ μ L'.L Q o C T (lore (trimP T R₁ δ β b))) (hO₁:O.threshold=R₁.threshold)(hO:O.B=R₁.B)
variable (G':Sun L' c f d (coneK L'.L vP τ) h z a a' m (pesto P₁ L' d (trunkM E₁ E₂ (haloK L'.L τ) 0 f)))
open Massive.Poised.TrainG PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open Planned.PrimaryIntegral295.Carrier
variable (N₀:Libretto su n)(V:Hera.Rights su n){E₀:Heir.Record}
variable (hWorks:Works P L'.L τ (L'.visit K d) T)(hPl:Plays N₀ E₀ P₂ R₁ P T τ)(hSeat: Seats H χ)
variable {Gh Gd Kq s₀ pL m₀ M0:ℕ}{brac μ₁ μ₂ A₀ A₁ A₂ T₀:ℝ}
variable (htV: β≥betaF su τ L'.L/2) (hΔ:|mm|≤ haloK L'.L τ)(hξ: R₁.threshold=fiery su τ L'.L)(hOc:R₁.B=highR L'.L τ)
variable (hg:L'.L.val ≥ m₀)(hPre:Prebit Q j k R₁.power Gd Dx P₂.power N₀ A₀ A₁ A₂ μ₁ μ₂ brac m₀)
-- don't write (S')
variable (hA:Ledger P₁ Q (Flight.visit L' K d).patch N₀ E₀ o μ C a vP h z a' m k Gn χ Θ V Gd k₁ R₁.power P₂.power R₁.order nL Dx A₀ A₁ A₂ τ)
variable (hK:0<u₀)(hw:0<t₀)(hX:u₀*t₀ ≤ φ)(hpF:φ ≤ A₀*x₀)(hv1:0<x₀)(ha:0<a)(hη:1 ≤ A₀)(hn:6 ≤ n)(hN:Gn<n)(hJ:4 ≤ k)
variable (hY:2*(radiusB τ+1)< f.val)(hvDx:2 ≤ Dx)(hvD:Gd ≤ Gn+1)(hvL:Gd ≤ nL)(ht:P₂.order=n)
local notation "CZ"=> tr
local notation "Ix"=> I✡
local notation "R★" p=> ((kindY).symm (Oq.ear p)).val
local notation "pu"=> brac*Massive.Poised.tipW N₀ V nL Gd A₁ A₂ (pup Gd A₂)
-- assumes one set of fonts. `N/θ fixed.One`. endpoint budgets B prior. Colony post and Arena. PUBLISHED Step theorem includes all of these, issued pre stage via cellarQ.MaxP and Vienna at every height.
open Massive.Poised.Stative
local notation "Φ!" i=> (fun s=> weight (d:=i) s)
local notation "d0"=> (Kit.slope L'.L)
local notation "s0"=> Girdle.price k₁ P₂.power P₂.order Dx nL
variable {Cz:ℝ} (hYt: T.R.A0=linesOf L' P.bind.penalty)(hKΓ:K=P.bind)(hZA:Laurent.size (cellar L'.L A - A') ≤ k₁)(hy: gateH k₁ τ≤c.val)
variable (hnL:Fintype.card (Massive.Poised.Palette.ZBand Gn)<nL)(hDg:Gn/2≤j)(htQ:Gn*Gn ≤P₂.power)(htY:Beacon.surface Gn≤Dx)
-- INPUT boundary data, estimated at same occurrence body.
variable {X0 X1 χ₁ aχ bχ aV bV μ₁' βY β' εR εB γ₂:ℝ}
variable (hXPub:Published Z Θ Dx nL μ₁' βY X0 X1)(hΩ:Pilot Θ Va Gn R₁.order R₁.power Dx nL r aχ bχ)
local notation "Ω0"=>Φ -- costs rare complement
local notation "Jt"=> (fun i:Jars Gn=> tr (Sum.inl i))
local notation "Jx"=> (fun i:E' => tr (Sum.inr i))
-- none
-- small PrC pre inequality.P.Tortue. roof comparison.S.c≥ large.N.IR.
open Massive.Poised.Carte.Hem
variable (heB:r+1≤R₁.B)(hBV: R₁.B≤2*radiusB τ)
lemma secondK (hB:R₁.B≥ r+1): coverNumber R₁.B (Massive.Poised.Carte.Hem.pot (r+1) f A) ≤ 81:=by
    exact (Corona.cover_mono (Corona.halo_mono (show r+1≤1*R₁.B from (one_mul R₁.B)|>.symm ▸ hB) (Subset.refl _)) _).trans (Corona.tile _ 1 R₁.B R₁.B_pos)
-- NEED actual `conversion` costs ratio.Co parameter.
variable (hL: (Footprint.preCost (Q.halo+8))+Footprint.conversion (L'.visit K d).ratio (Q.halo+8)*81 ≤ radiusB τ)
include Qe hM hB hO hL heB hBV
open Kit Kites
lemma sunk (i:Jars Gn): warmA L' d K H G U Γ Qx Tq Oq A φ X F' (χ:=χ) (tr (.inl i)):=by
   let q:= (Sum.inl i : Jars Gn⊕E'); let v:= tr q; let d':= (kindY).symm (Oq.ear q); refine ⟨d'.val,tower_step ..,?_⟩
   have hK : coverNumber R₁.B (Massive.Poised.Carte.Hem.pot (r+1) f A) ≤81:=by
       exact (Corona.cover_mono (Corona.halo_mono (show r+1≤1*R₁.B from (one_mul R₁.B)|>.symm ▸ heB) (Subset.refl _)) _).trans (Corona.tile _ 1 R₁.B R₁.B_pos)
   let H':=trunkP H S₁ _ _ F' d'.val
   have he:= terrestrial H S₁ (Z') P₀ F' d' le_rfl (hO.symm ▸ hBV) (hB ▸ P₂.B_pos)
   rw [show col _ _ _ _ d'=Oq.ear q from (kindY).apply_symm_apply _,Oq.homeP,hO] at he
   have hz:coverNumber R₁.B ((roll 6 (Qx)).addr q).support≤81:=hK
   have hu:0 ≤ Footprint.conversion (L'.visit K d).ratio (Q.halo+8):= by unfold conversion; unfold Footprint.preCost; positivity -- check
   exact_mod_cast he.trans ((add_le_add_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hz) hu) _).trans hL)
local notation "Ω"=> Era (P₁:=P₁) (T:=T) (τ:=τ) (o:=o) L' d K (a:=a) (Q:=Q) (z:=z) (h:=h) (a':=a') (C:=C) (μ:=μ) (m:=m) (vP:=vP) R₁ P₂ Cz Dx n k₁ Gn nL A₀ μ₁ μ₂ Θ χ
variable (hPV:30*(r+1)≤ f.val) (hD:Gn+1≤nL)
local notation "Γf"=> Cz*Real.exp (μ₁*81)*bχ -- pre.L. φ maybe.N;
local notation "U'"=>u₀*t₀
include hWorks hO₁ hSeat htV hΔ hξ hOc hK hw hX hpF hv1 ha hη hn hN hY hvDx hD hR F₁ G' hYt hKΓ hZA hy hnL hDg htQ htY hJ
variable (hCB:0 ≤ Cz)(hμ:0≤μ₁)(hs:81 ≤ R₁.B)(hv₀:1 ≤ u₀)(hv:1 ≤ x₀)
include hΩ hCB hμ hs hv hPV hSup
set_option maxHeartbeats 630000 in
lemma scoredE (Bq:Ω) (i:Jars Gn):
   let U:=Jt i
   ∃ t:ℝ, Flame (Z✡ U) P₂ ((Q✡) U) t✡ u₀ Dx nL t ∧ t*Real.exp (μ₂*coverNumber P₂.B ((Q✡) U))≤ Γf* Kit.slope L'.L^weightJ i*princS Xb i R₁ x₀ ∧ ∀ y:Label Gn, Beacon.ActionTest Θ A' (Z✡ U) y.val →∀ p:Rings Gn, Massive.UV.weight p.val≤ weightJ i→ ‖Stative.fare p y.val P₂.threshold u₀- (Kit.slope L'.L:ℂ)^Massive.UV.weight p.val*Stative.fare p (gradeCut Gn i.val Xb).val P₂.threshold (u₀*t₀)‖ ≤2*relief L'.L τ*bχ *princS Xb i R₁ x₀:=by
    intro Y₁; let u:= (Sum.inl i:Jars Gn⊕E'); let φi:= gradeCut Gn i.val Xb; have hG:(Qx).fill u=Orientation.graphs (c:=f) _ _ _ φi:=rfl
    have hW:Beacon.ActionTest Θ A ((Qx).fill u) φi.val:=hΩ.tested _ A _ hPV
    have hi:= Facets.Saturated.engraved (cut_afford Xb i) Θ A _ hW (weightJ i) le_rfl (le_trans (jar_w i) (by omega))
    let X0:= princS Xb i R₁ x₀; let z':= bχ * X0; have hF : Flame ((Qx).fill u) R₁ ((Qx).addr u).support (wrap f A) x₀ Dx nL z':= primCost hΩ rfl rfl hv hPV i
    have hx': coverNumber R₁.B ((Qx).addr u).support ≤81:= by
       exact (Corona.cover_mono (Corona.halo_mono (show r+1≤1*R₁.B from (one_mul R₁.B)|>.symm ▸ heB) (Subset.refl _)) _).trans (Corona.tile _ 1 R₁.B R₁.B_pos)
    obtain ⟨h₁,h₂⟩ := oak_area L' d K H G U Γ (Qx) (Tq) Oq A A' Qe φ X hM F' hSup hB hR Θ F₁ hO₁ hO G' hWorks hSeat htV hΔ hξ hOc hK hw hX hpF hv1 ha hη hn hN hJ hY hvDx (le_trans (jar_w i) (by omega)) hYt hKΓ hZA hy hnL hDg htQ htY u (sunk L' d K H G U Γ A Z Tρ Oq Qe φ X hM F' hB hO heB hBV hL i) hF hi hD Bq -- inspect sink signature. angle hχ delta
    -- `hD` positions key
    let c0:ℝ:=coverNumber B (Q✡ Y₁); let c1:ℝ:=coverNumber R₁.B ((Qx).addr u).support; let g:ℝ:= Kit.slope L'.L ^ weightJ i; have hg:0≤g:=pow_nonneg (Kit.slope_pos _).le _
    refine ⟨_,h₁,?_,fun y hy v hv=> (h₂ v (hx'.trans hs) φi y hW hy hv).trans_eq (by unfold z'; change _*(_*_)=_; ring)⟩
    rw [hB]; have hz:0 ≤ z':= hF.sight.travels; have hf: 0 ≤ g*Cz*z':=mul_nonneg (mul_nonneg hg hCB) hz; change g*Cz*Real.exp (μ₁*c1-μ₂*c0)*z'*Real.exp (μ₂*c0) ≤ Γf*g*X0
    calc
       _= (g*Cz*z')* Real.exp (μ₁*c1):=by rw [Real.exp_sub]; field_simp
       _ ≤ (g*Cz*z')* Real.exp (μ₁*81):=mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (by unfold c1; exact_mod_cast hx') hμ)) hf
       _ = _ := by change g*Cz*(bχ*X0)*_= _ ;ring
end Drawing.Claro
end YM.MassiveQCD.Lyre
#print axioms YM.MassiveQCD.Lyre.Drawing.Claro.scoredE
