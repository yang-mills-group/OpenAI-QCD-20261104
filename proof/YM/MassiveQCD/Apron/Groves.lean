import YM.MassiveQCD.Apron.Palt
set_option linter.unusedSectionVars false
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
open Sway OrbitG Ribbon
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
variable {j k m i k₁ n:ℕ}
variable {z η p h a a' hQ v δ b s u q:ℝ}{P' : Plan k}{X:Run.St f}
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
noncomputable def vantage : Fleet H (Wound (Zⁱ) ⊕ Varn f c⊕Gaze c) (Ribbon.ample N I):= united (Y') (united (U') (X'))
-- entitlement knots FACTS includes legacy offers geometry. Need broadcast `vantage` eligibility irrespective of spent E masks.
local notation "Vx" => tableau L' d K P₀ H G U Γ
local notation "Tx"=> vantage L' d K H G U Γ Y A φ
local notation "Uq"=> deckHue H (Z') P₀ (Zⁱ)
variable (F:Tree.Forest (Flight.visit L' K d).ratio) (θ:ℝ)
local notation "a₂"=> shiftCost L'.L τ (romp L'.L)
local notation "p₁"=> demandQ L'.L θ τ
local notation "UC"=> unitsP Q L'.L μ β τ C a₂ p₁
namespace Grove
-- Flex over augmented & actual systems in same budget. Many levels not supplied yet. Uses all loans downstream as `Vantage.Wake`. Includes actual Phantom.N-Signs.Paid β.State.Up.Anal.
structure Shed (Ω: Tree.Forest (Flight.visit L' K d).ratio) (Y:Fleet H ι N) (φ θ:ℝ):Prop where
    within :let P:=Y.suitcase Ω; let b:=unitsP Q L'.L μ β τ C (shiftCost L'.L τ (romp L'.L)) (demandQ L'.L θ τ); ∃ w,P.Depth b w (fun _=>0) ∧ Summable w ∧ (∀ V:Grid c,P.solves V)∧ P.Merit w (shiftCost L'.L τ (romp L'.L)) (token c N φ)
-- serve startup.R. prices signature imported; categorical lemma transport.
variable {t q₀:ℝ}{q₁:I→Bool}{p:D→ℝ}{e:E→ℝ}{κ:J→ℝ}{wt: Tr f→ℝ} -- Tr path
variable (hw:Y.Wave O.threshold q₁ A)
local notation "s0"=> mintD H (Z') P₀ (Zⁱ) wt e κ q₀
local notation "φz"=> (18*B)
local notation "vU"=> fan L'.L (1/4) τ
variable (hh:Y.Coins e κ t O.threshold)(hr:Peak (G.equip N (radiusB τ)) O.threshold t φ q₀ wt)(hδ:0<δ)
include hw hh hr hδ
-- certificate
lemma shaper (he: (Tx).Famous){s1:Varn f c→ℝ}{s2:Gaze c→ℝ} (h1: Fleet.Theft (VarnC H U N) F (fun i=>siteH i (S').ratio) s1 φ vU (univ.filter fun i=>waxV i=none) φz ((S').ratio.count.val^4+1)) (h2:Fleet.Theft (sailP H Γ N) F Prod.fst s2 φ vU (univ.filter fun i=> i.2=none) φz 1) (hB:0<B) (p0:Ac.Hit (Uq).ground B s0 Q.relative (bootstrut L'.L θ τ))(p1:Ac.Hit (VarnC H U N).ground B s1 Q.relative (betaF su τ L'.L ^ (-(3/8):ℝ)))(p2:Ac.Hit (sailP H Γ N).ground B s2 Q.relative (betaF su τ L'.L ^ (-(3/8):ℝ))) (hv:1≤φ)(hD:(UC).Buy L'.L Q.halo B): Shed L' d K H F (Tx) φ θ ∧ (Tx).Feasible:=by
    let A':= Y'; let A₁:= U'; let A₂:= X'; let E:=Tx
    have hp:=certify (F:=F) H (Z') (Zⁱ) Y A φ hw ((roofs (Z') P₀ 30 B le_rfl hB).1) hh hr hδ hv p0 (show 0≤Q.relative from by unfold Target.relative; linarith [Q.bound,Q.usable,Q.pos]); obtain ⟨hs,hm,hK⟩:=hp
    let sX:=Sum.elim (s0) (Sum.elim s1 s2); have hx:= balanceP (united A₁ A₂) (steals (F:=F) H (Z') (Zⁱ) Y A φ hw hh hr hδ (fun _=>0) (fan_pos L'.L (1/4) τ).le 0 0) (balanceP A₂ (gait I _ h1) (gait I _ h2)); let pT:= (Tx).suitcase F
    have hP : Ac.Hit pT.ground B (tariff sX (fun _=>0) (fun _=>0) Q.ε) Q.relative p₁:=by
       rw [show tariff sX (fun _=>0) (fun _=>0) Q.ε=sX by ext; simp [tariff]]; exact Labels.together _ _ _ p0 (Labels.together _ _ _ p1 p2)
    have hF: pT.Merit sX a₂ (token c M φ):=by
       have hv:=watch _ hx; rw [show max 0 (max (18*B) (18*B))=18*B by omega, show 0+((Flight.visit L' K d).ratio.count.val^4+1+1)=romp L'.L by rw [zero_add]; rfl] at hv; exact hv
    refine ⟨⟨sX,surveyP pT rfl hx.grow (fun _=>le_rfl) _ _ hD hP,Summable.sum _ hs (hasSum_fintype _).summable,fun v=>legible H A' (united A₁ A₂) v (hm _) he,hF⟩,?_⟩
    obtain ⟨hp⟩:=Villa.validH L' K d H G U P₀ (Γ:=Γ) hB; constructor; rintro (i|i|i) U V h
    · exact hK.spark i U V h -- signature
    · refine hp (.inr (.inl i)) U V ?_; intro hh; apply h; exact (congr_arg (bearing I c N) hh).trans (map_zero _)
    -- same
    refine hp (.inr (.inr i)) U V ?_; intro hh; apply h; exact (congr_arg (bearing I c N) hh).trans (map_zero _)
end Grove
end YM.MassiveQCD.Apron
