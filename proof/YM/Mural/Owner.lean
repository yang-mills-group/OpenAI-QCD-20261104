import YM.Mural.Sappy
import YM.Mural.Fane
import YM.Mural.Orla
/-!
# Single-component steep log estimate and projection reports at full volume.
 Optional tweak in the shelf of post-noise legs receives separate single-vertex funding; this will fit a path *difference* before integrating both sorts of fields.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Apron
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon QCD.Mural
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
variable {j k m i k₁ n:ℕ}{z η p h a a' hQ v δ b s u q:ℝ}{P' : Plan k}{X:Run.St f}
open QCD.Acre QCD.Mural Glow
variable (L':Flight j k)(d:f.val=c.val*L'.L.val)(K:KernelChoices)
local notation "S'"=> Flight.visit L' K d
variable {T:Tube su (Flight.visit L' K d)}{W' :ℕ→Atom su 2}
variable (H:Cash W τ μ L'.L Q o C T (trimP T O δ β b))
variable {P₀:Rise f N E J} [Countable E][Countable J]
variable (G:Sun L' c f d η h z a a' m X) (U :Swathe L' d X W' P' h η a u v i)
variable (Γ:Land c (Site c) (Site c)){D':Pays c (Site c) (Site c)}
variable [Fintype I] (Y:Stitch.Tablet P₀ I)(A:I→Site f)(φ:ℝ)
local notation "M"=> Ribbon.ample N I
local notation "R'"=> trimP T O δ β b
local notation "B"=> radiusB τ
local notation "M'"=> highR L τ
local notation "Z'"=> G.equip N (radiusB τ)
local notation "Zⁱ"=> roof (G.equip N (radiusB τ)) P₀ 30 B
local notation "Y'" => closet H (G.equip N (radiusB τ)) (Zⁱ) Y A φ
local notation "U'" => loommark I (VarnC H U N)
local notation "X'" => loommark I (sailP H Γ N)
local notation "Tx"=> vantage L' d K H G U Γ Y A φ
local notation "Uq"=> deckHue H (Z') P₀ (Zⁱ)
-- optional variation modifies only mantle.working; same indices. Keep Gamma equality synt
variable (uV : Varn f c → Grid f→Grid c→EvenA c (Ribbon.ample N I))
noncomputable def mantel :Fleet H (Wound (Zⁱ)⊕ Varn f c⊕ Gaze c) (Ribbon.ample N I):=united (Y') (united (Fleet.align (U') uV) (X'))
local notation "Tv"=> mantel L' d K H G U Γ Y A φ uV
open Apron.Grove NormedSpace Stitch Tablet
variable {x χ θ ξ α h':ℝ} {q':I→Bool} (he:Y.Flora O.threshold q' A)
-- Hoop appointment optionally allows a mantle target exactly. Lens communicates true funding throughout. Mostly h callable for ANY configuration.
open scoped PhysicalNext.Repeat.Greenbelt
open PhysicalNext.Repeat.Greenbelt
local notation "siz"=> storm L'.L τ
local notation "G'"=> diceV Q L'.L μ C θ β τ
local notation "s'"=> fundsL L'.L θ τ
local notation "tt"=> fan L'.L θ τ
local notation "fe"=> payFee Q L'.L θ τ
local notation "se"=> fan L'.L (1/4) τ
local notation "Gz"=> family c N I
variable {gv:Gaze c→ℝ} (Dq:Porch L' d K H G U Γ N θ φ α (1/32)) (hf:Y.Flora O.threshold q' A)
structure TicketV (x θ α:ℝ) (uV: Varn f c→ Grid f→ Grid c→EvenA c (ample N I)) :Prop where
 house : (mantel L' d K H G U Γ Y A φ uV).Famous
 title : Corner Q (radiusB τ) (diceV Q L'.L μ C θ β τ) α
 sturdy : (mantel L' d K H G U Γ Y A φ uV).Feasible
 gator : (mantel L' d K H G U Γ Y A φ uV).gator
 speech : (mantel L' d K H G U Γ Y A φ uV).speaking
 level : ∀ F:Tree.Forest (Flight.visit L' K d).ratio,
      let P:=(mantel L' d K H G U Γ Y A φ uV).suitcase F
      ∃ w,P.Depth (diceV Q L'.L μ C θ β τ) w (fun _=>0) ∧ Summable w ∧ (∀ V:Grid c,P.solves V)∧
           P.Merit w (storm L'.L τ) (token c (Ribbon.ample N I) φ) ∧ P.Merit w (storm L'.L τ) (paidM (family c N I) x 4 φ)
 counts : 1≤φ

-- Unmarked at Sail canonical. Varn guardian receives ONE more meter appointment. Even for non-birth Tick user can just take standard Varn receipts unchanged. Ω *full* not Shelf.Use when Waltz upgrades PP network.
variable {p₀ p₁ pe:E→ℝ}{q₀ q₁:J→ℝ}
variable (hW:Y.Wave O.threshold q' A)
variable (hP:Cents P₀ p₀ q₀ (fan L'.L θ τ) O.threshold) (hD:Fill P₀ p₀ q₀ (1/32) (1/32) (taxK L'.L τ 1) 1 (Jets.Touch.chip L'.L τ) (highR L'.L τ))
variable (hX:P₀.Wave O.threshold)(hRe:P₀.Reframe) (hT: Cents P₀ pe q₁ (fan L'.L θ τ) O.threshold)(hΩ: Fill P₀ pe q₁ (1/32) (1/32) (taxK L'.L τ (7/8)) 1 (chipV L'.L τ) (highR L'.L τ))
variable (w₀:Site f) (h₀:Ac.Hit (fun i:E=> (P₀.row i).support) (highR L'.L τ) p₁ (1/32) (payFee Q L'.L θ τ))(ht:0≤p₁)(hA:∀i:E,p₁ i≠0 → w₀∈(P₀.row i).support∧pe i=0) (hΓ:Firm 4 Y x (pe+p₁) q₁ (fan L'.L θ τ) O.threshold)
variable (hR:Footprint.reserve (1/32) (Q.relative+1) (conversion (sliceL L' d) 38) ξ)
variable (hS: (Fleet.align (loommark I (VarnC H U N)) uV).Famous)
variable (hg: (Fleet.align (loommark I (VarnC H U N)) uV).gator) (hk:(Fleet.align (loommark I (VarnC H U N)) uV).Feasible)
variable (hv:(Fleet.align (loommark I (VarnC H U N)) uV).speaking) (hd:(loommark I (sailP H Γ N)).speaking)
variable (hw:∀ U:Grid f,∀ g:Frame f,(∀ i,g ((L'.visit K d).ratio.embed i)=1) →∀ i:Wound (roof (G.equip N (radiusB τ)) P₀ 30 (radiusB τ)),Y.hue O.threshold (G.equip N (radiusB τ)) i.val (gauge g U)= Y.hue O.threshold (G.equip N (radiusB τ)) i.val U)
variable (hBills:∀ F:Tree.Forest (Flight.visit L' K d).ratio,
   ∃ (u:Varn f c→ℝ)(v:Gaze c→ℝ)(S:Finset (Varn f c)),
    Vigil (Fleet.align (loommark I (VarnC H U N)) uV) (family c N I) F (fun i=>siteH i (Flight.visit L' K d).ratio) u x 4 φ (fan L'.L (1/4) τ*2) S (18*radiusB τ) (L'.L.val^4+2)
    ∧ Vigil (loommark I (sailP H Γ N)) (family c N I) F Prod.fst v x 4 φ (fan L'.L (1/4) τ*2) (univ.filter fun i=> i.2=none) (18*radiusB τ) 1
    ∧ Ac.Hit (Fleet.align (loommark I (VarnC H U N)) uV).ground (radiusB τ) u Q.relative (2*fundsL L'.L θ τ) ∧ Ac.Hit (sailP H Γ N).ground (radiusB τ) v Q.relative (2*fundsL L'.L θ τ))
variable (hb:(diceV Q L'.L μ C θ β τ).Buy L'.L Q.halo (radiusB τ)) (hc:Corner Q (radiusB τ) (diceV Q L'.L μ C θ β τ) α)
-- Tough Frame
include hf Dq hP hD hX hRe hT hΩ w₀ h₀ ht hA hΓ hR hS hg hv hd hw hBills hb hc hk
set_option maxHeartbeats 600000 in
lemma permitsV (he: 1 ≤x)(hp:fe ≤1)(hM:B>0)(hM':highR L'.L τ≤ 2*radiusB τ)(hu:degreePrice (radiusB τ) (2*(fundsL L'.L θ τ)) 1 ≤1/2) (hs:1 ≤ fan L'.L θ τ) : TicketV L' d K H G U Γ Y A φ x θ α uV:=by
     have hκ : 0 ≤ Q.relative:=by unfold Target.relative; linarith only [Q.bound,Q.pos,Q.usable]
     let XU:= VarnC H U N; let X0:= deckHue H (Z') P₀ (Zⁱ); let Y₀:= Y'; let A₂:= X'; let A₁:= Fleet.align (U') uV
     obtain ⟨r,h₁,h₂⟩:= Dq.stoves P₀ p₀ q₀ hP hD; obtain ⟨h₃,h₄⟩:=h₂ pe q₁ hT hΩ
     let t0:= pe+p₁; let Υ:=tenderP G N B tt φ (lantern L'.L τ); let δ0:=taxK L'.L τ (1/2); have h0:0 ≤ t0:=fun i=>add_nonneg (hT.pos _) (ht i)
     have hz:=roofs (Z') P₀ 30 B le_rfl hM
     have hj : Ready (Zⁱ) B (paidSet (Z') P₀ Υ t0 q₁ r 1 δ0 1) Q.relative (2*s') 1 (1/2):=by
        have hSt:= feePower L'.L θ Q τ -- order
        refine step_income (Z') Zⁱ w₀ h₄ h₀ hA hR ?_ hu (fun i:E=> by convert! hz.2 (Sum.inr (Sum.inl i)) using 1) Dq.haze (Real.exp_pos _).le hT.non (zero_le_one.trans h₁.post) hSt.1.le hT.pos ht hp (by norm_num) hM hM'
        calc s' + Real.exp 1*_ = s'+s':= by congr 1; rw [← mul_assoc,mul_comm,hSt.2.1]
             _ ≤ 2*s':=by linarith
     have hδ:= Dq.room.1; let v0:= fan L'.L θ τ; have hPC: Cents P₀ t0 q₁ v0 O.threshold:=by
        refine ⟨h0,hT.non,fun i U=>(hT.cost _ _).trans (le_add_of_nonneg_right (ht i)),hT.funds⟩
     have hQ:∀ U (s:Finset (Fj (Tr f) E J)),Mild (Tablet.tunnel (Z') s U):= fun U s=> banked B N G s U
     let w:=mintD H (Z') P₀ Zⁱ Υ t0 q₁ r
     have hf₀:Ac.Hit (Uq).ground B w Q.relative (4*s'):=by
        have hp:= revenueX H (Z') P₀ (Zⁱ) h₃ hPC hX hj le_rfl (Real.one_le_exp (mul_nonneg (by norm_num) (fan_pos ..).le)) hδ Dq.room.2.1 hκ
        convert! hp using 1
        ring
     have hh0:=certPort (F:=Classical.choice (Tree.select (S').ratio L'.odd)) H (Z') (Zⁱ) Y A φ hf hz.1 hΓ h₃ hδ he hQ Dq.loft hf₀ hκ
     have h0P:= homeP H (Z') P₀ (Zⁱ) h₃ hPC hX hδ rfl Dq.loft (fun UU g he s=>fowl H P₀ L' d G UU g he B hRe s)
     have hFamous:Y₀.Famous:= ensembleF H (Z') (Zⁱ) Y A φ hf hΓ h₃ hδ he hQ h0P Dq.loft hw
     have ht':=hFamous; -- keep binder
     have h₁A:=Dq.pumps; let he_:=jungle Y₀ (united A₁ A₂) ht' (jungle _ _ hS (loping I _ h₁A.2.1))
     have hFv:(Tv).Feasible:=by
         constructor; rintro (i|i|i) U V h
         · exact hh0.2.2.spark i U V h
         · exact hk.spark i U V h
         refine Finset.Nonempty.mono (halo_subset ..) (?_); exact Finset.Nonempty.mono (seaP i B _) (halo_subset _ _|> fun h=>Finset.Nonempty.mono h (singleton_nonempty _))
     refine ⟨he_,hc,hFv,entwine Y₀ (united A₁ A₂) (residentF H _ (Zⁱ) Y A φ hf hz.1) (entwine _ _ hg (lofty I _ h₁A.2.2.2)),?_,fun F=>?_ ,Dq.loft⟩
     · rintro (i|i|i); exact factorsA H _ (Zⁱ) Y A φ hf i; exact hv i; exact hd i
     obtain ⟨W₁,W₂,S,hE,hV,hP,hT⟩:= hBills F; let bP:= se*2; have hy:0< φ:=zero_lt_one.trans_le Dq.loft
     have hN:0<s':=fan_pos ..
     have hx:= posting Y₀ _ (polling (F:=F) H _ (Zⁱ) Y A φ hf hΓ h₃ hδ he hQ (fun _=>0) (show 0 ≤ bP from mul_nonneg (fan_pos ..).le zero_le_two) 0 0) (posting A₁ _ hE hV)
     let Qz:= Sum.elim w (Sum.elim W₁ W₂)
     have hR : Ac.Hit (Tv).ground (radiusB τ) Qz Q.relative (4*s'+(2*s'+2*s')):= Labels.together _ _ _ hf₀ (Labels.together _ _ _ hP hT)
     let P:= Y₀.suitcase F; have hH:∀ V:Grid c,P.solves V := (certPort (F:=F) H (Z') (Zⁱ) Y A φ hf hz.1 hΓ h₃ hδ he hQ Dq.loft hf₀ hκ).2.1
     let yQ:=((mantel L' d K H G U Γ Y A φ uV).suitcase F); have hI:Ac.Hit yQ.ground (radiusB τ) (tariff Qz (fun _=>0) (fun _=>0) Q.ε) Q.relative (drafts L'.L θ τ):=by
        rw [show tariff Qz (fun _=>0) (fun _=>0) Q.ε=Qz by ext; simp [tariff]]; exact fun i=>budget_loosen (hR i) (by unfold drafts; linarith only [hN])
     have hxy : bP*(↑(Animals.ballCost ((max 0 (max (18*radiusB τ) (18*radiusB τ)))+1))*(0+(L'.L.val^4+2+1):ℕ))=storm L'.L τ:=by unfold storm; rw [max_self,max_eq_right (Nat.zero_le _),Nat.zero_add]; congr 2 -- edit
     have hey:= sans _ _ hx hy he
     have h:= watch _ hey; have h':= refined _ _ hx he hy
     rw [show _ = storm L'.L τ from hxy] at h h'
     refine ⟨Qz,yQ.surveyP rfl hx.rise (fun _=>le_rfl) (storm ..) _ hb hI,Summable.sum _ hh0.1 (hasSum_fintype _).summable,fun V=>legible H Y₀ (united A₁ A₂) V (hH _) he_,h,h'⟩
end YM.MassiveQCD.Apron
#print axioms YM.MassiveQCD.Apron.permitsV
