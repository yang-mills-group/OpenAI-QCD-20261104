import YM.Cardinal.Earning
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
namespace Drawing
open Massive.Poised QCD.Shells Cupola Plate Card Iris Puff Patron
open Ac QCD.Cove.Send Warmlet Push.Local Massive.Poised.Plans Massive.Poised.Plans.Stamp
open Massive.UV
variable {E' K':Type}{q': Bool}
-- Pu.6
variable (A A' :Cover) {x₀:ℝ} {Gn r :ℕ}{Ua:YM.Source.Hol su} {Va:YM.Massive.Lining.Temper.Collage.Exhibit Ua}{R₁:BudgetPoint}{Xb:Label Gn} (Z: CentreFrame (c:=f) R₁ x₀ Xb q' Va A (r+1) E' K') (Oq:Twist.Register P₀ (Puff.roll 6 (ritual Z)) Z.spine)
variable (Qe: Seal 6 (wrap f A) (ritual Z))
local notation "Qx"=> ritual Z
set_option quotPrecheck false
local notation "Tq"=> Z.spine
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
variable {χ:Chi}{α ξ θ t t₀ x x₁ κ α₁ α₂ ε:ℝ}{P₂: BudgetPoint}
variable (X:Clusters (vantage L' d K H G U Γ (Twist.result P₀ (Puff.roll 6 (ritual Z)) Z.spine Oq) (fun (_:Unit)=>wrap f A) φ).Bright → RegularAddress c)
variable (hM:∀ i,(X i).support= GasP.seatP ((vantage L' d K H G U Γ (Twist.result P₀ (Puff.roll 6 (ritual Z)) Z.spine Oq) (fun _:Unit=>wrap f A) φ).lightF) i)
variable (F':Cash W τ μ L'.L Q o C T (lore (trimP T O δ β b)))
local notation "Cⁱ"=> crude Tx χ X
local notation "a⁺"=>  budAtlas (A⁺) (30*B)
local notation "I✡"=> Reel.Answer 6 (A⁺) (Cⁱ) (χ') Set.univ
local notation "E✡"=> (Reel.render 6 (A⁺) φ t₀ Cⁱ (χ') Set.univ)
local notation "Z✡"=> Reel.speaker (qᴮ) (E✡)
variable (hSup:Supplies L' d K H G U Γ (Twist.result P₀ (Puff.roll 6 (ritual Z)) Z.spine Oq) (fun (_:Unit)=>wrap f A) φ χ (fun _=>q') t θ P₂.order P₂.power)
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
local notation "Uⁱ"=> A⁺ ()
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
-- NEED actual `conversion` costs ratio.Co parameter.
variable (hL: (Footprint.preCost (Q.halo+8))+Footprint.conversion (L'.visit K d).ratio (Q.halo+8)*81 ≤ radiusB τ)
include Qe hM hB hO hL heB hBV
open Kit Kites
local notation "Ω"=> Era (P₁:=P₁) (T:=T) (τ:=τ) (o:=o) L' d K (a:=a) (Q:=Q) (z:=z) (h:=h) (a':=a') (C:=C) (μ:=μ) (m:=m) (vP:=vP) R₁ P₂ Cz Dx n k₁ Gn nL A₀ μ₁ μ₂ Θ χ
variable (hPV:30*(r+1)≤ f.val) (hD:Gn+1≤nL)
local notation "Γf"=> Cz*Real.exp (μ₁*81)*bχ -- pre.L. φ maybe.N;
local notation "U'"=>u₀*t₀
include hWorks hO₁ hSeat htV hΔ hξ hOc hK hw hX hpF hv1 ha hη hn hN hY hvDx hD hR F₁ G' hYt hKΓ hZA hy hnL hDg htQ htY hJ
variable (hCB:0 ≤ Cz)(hμ:0≤μ₁)(hs:81 ≤ R₁.B)(hv₀:1 ≤ u₀)(hv:1 ≤ x₀)
include hΩ hCB hμ hs hv hPV hSup
-- Revenue stages. `B` bounty.R output. 
local notation "Aw"=>A⁺ ()
local notation "Q0"=> Reel.Book (A⁺) (qᴮ) E✡
local notation "t'"=>roomy L' d K H G U Γ (ritual Z) (Z.spine) Oq A A' φ X hM hSup hR hp
local notation "Off" i=> ¬ ((κ') i∧ i∈Set.range (tr)) -- notation κ' def macro π
local notation "Cv"=> Reel.voiceE (Dx*nL) 1 B*(Δ*Φ+Ψ)+ (Girdle.price (wiCost B) P₂.power P₂.order Dx nL*crownCost Dx nL B)*κ
local notation "Av"=> Fintype.card (Rings Gn) * (2*relief L'.L τ) -- implicit type coe? Fintype.card ℝ via ↑ expected. 
local notation "ℓP"=> 2*relief L'.L τ*bχ
local notation "Ce" => (Kit.slope L'.L^(Gn+1)*Cz)*X0
open Incidence
-- damping h
variable (HVx:∀ i':Jars Gn⊕E', Sight ((ritual Z).addr i').support (wrap f A) 2 R₁ x₀ ((ritual Z).fill i') (σ (Oq.ear i'))) (hTT:Pilot Θ Va Gn P₂.order P₂.power Dx nL r aV bV)
-- ⚠ h shadow already bound h:ℝ. rename
variable (haQ:μ₁ ≤ μ₁')(hbA: 0 ≤ μ₂)(hα: Real.exp ((μ₁-μ₁')*R₁.B)*(aV * (Kit.slope L'.L^(Gn+1)*Cz)) ≤ χ₁)
include HVx hTT hα haQ hXPub hv₀ hbA hp
-- EXACT protocol.Body.Seq.Warning:
set_option maxHeartbeats 720000 in
lemma funds (Bq:Ω)(h0: Patrol (O₁:=R₁) L' d K H G U Γ Y Aᴮ φ F' χ P₂ x₀ μ₂ κ qᴮ σ) (g:I✡→ℝ)(h1: Mantle L' d K H G U Γ (Qx) Tq Oq A A' φ X F' g (αe:=μ₂) (k₁:=k₁) (ε:=ε) (P₂:=P₂) (u₀:=u₀) (t₀:=t₀))(Vp:Puff c 6 I✡ q')(hx:∀ i,Vp.fill i=Reel.speaker qᴮ E✡ i) : Scenes q' Vp Q✡ Jt Θ P₂ R₁ u₀ 1 x₀ (U') (d0) Γf (Ce+Cv) μ₂ μ₁ ℓP ((max Av χ₁)*X0+aV*Cv) Xb A' Dx nL :=by
    obtain ⟨F₁o,hB0,hG⟩:= outward L' d K H G U Γ (Qx) Tq Oq A A' φ X hM F' hSup hB hR hp hK Dx nL g h1 -- order
    obtain ⟨F₂o,hR',hY'⟩:= nearWard (Dx:=Dx) (nL:=nL) L' d K H G U Γ (Qx) Tq Oq A A' Qe φ X hM F' hSup hB hR hp R₁ σ hX hw hK HVx h0 -- Dex implicit unresolved name from call. add
    obtain ⟨g0,hg0,hQ0⟩:=hXPub.costs
    let I₀:= I✡; let P:= fun i:E'=> (Z.p.addr i).support; let Rt:= Q✡; let T:I₀→Prop:= κ'; let R i:= (tr i); 
    have hm:Sum.elim Jt Jx=tr:=funext fun i=> by rcases i with i|i <;> rfl
    have hp'(i:I✡): wrap c A'∈ Rt i:= (grows L' d K H G U Γ (Qx) Tq Oq A φ X hM F' _).1 (locus_area L' d K H G U Γ (Qx) Tq Oq A A' φ X hM hSup hR hp i)
    have hf:∃ (f:I₀→ℝ),(∀ i:I₀, (¬(T i ∧ i∈ Set.range R))→ Flame (Vp.fill i) P₂ ((Q✡) i) t✡ u₀ Dx nL (f i))∧ Ac.Hit Rt P₂.B f μ₂ Cv:=by
        refine ⟨fun i=> F₁o i+F₂o i, fun i hh=>?_,fun i=>?_⟩
        · 
          have hs:wrap c A'∈(Q✡) i:=hp' i; rw [hx]; by_cases hv:T i;
          · have h:= hY' i hv (fun hk=> hh ⟨hv,hk⟩); apply Facets.leFlame h; apply le_add_of_nonneg_left; exact (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 ((hit_collect t✡ Q✡ _ hp' hB0).1 i) -- namespace
          apply Facets.leFlame (hG i hv); apply le_add_of_nonneg_right; exact (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 ((hit_collect t✡ Q✡ _ hp' hR').1 i)
        have h:=budget_plus (hB0 i) (hR' i); unfold Rt; rw [hB]; convert! h using 1; ext j; split; exact add_mul ..; exact (add_zero _).symm
    have hl(i:E')(he:T (Jx i)) : Flame (Vp.fill (Jx i)) P₂ (Rt (Jx i)) t✡ u₀ Dx nL ((Kit.slope L'.L^(Gn+1)*Cz)*Real.exp (μ₁*coverNumber R₁.B (P i)-μ₂*coverNumber P₂.B (Rt (Jx i)))*g0 i) ∧(coverNumber R₁.B (P i) ≤ R₁.B →∀ (p': Label Gn), Beacon.ActionTest Θ A' (Vp.fill (Jx i)) p'.val → wealth p'.val P₂.threshold u₀ ≤ Av*g0 i):=by
       let u:= (Sum.inr i:Jars Gn⊕E'); have hW(u):=hXPub.key u; let z:= (0:Label Gn); have hh(a:PowerPair Gn): Stative.coord a z.val=0:=map_zero _
       have ht:= Facets.Saturated.engraved (x:=z) (Facets.Saturated.mk (w:=Gn+1) (l:=0) (e:=0) fun k h=> (h (hh _)).elim) Θ A ((Qx).fill u) (hW i) (Gn+1) le_rfl le_rfl
       have hQ : Flame ((Qx).fill u) R₁ ((Qx).addr u).support (wrap f A) x₀ Dx nL (g0 i) := by
           have h:= hg0 i; exact h
       obtain ⟨h₀,h₁⟩:= oak_area L' d K H G U Γ (Qx) Tq Oq A A' Qe φ X hM F' hSup hB hR Θ F₁ hO₁ hO G' hWorks hSeat htV hΔ hξ hOc hK hw hX hpF hv1 ha hη hn hN hJ hY hvDx le_rfl hYt hKΓ hZA hy hnL hDg htQ htY u he hQ ht hD Bq
       rw [hx,hB]; refine ⟨h₀,fun hs p' hX=>?_⟩; unfold Plans.wealth; calc
         _ ≤ ∑ i':Rings Gn,(2*relief L'.L τ)*(g0 i) :=Finset.sum_le_sum fun j _=>by
                 have ht':Massive.UV.weight j.val ≤ Gn:= (Set.Finite.mem_toFinset (weightFinite Gn)).mp j.property
                 have h :=h₁ j hs z p' (hW i) hX (by omega); rw [show Stative.fare j.val z.val _ _=0 from (by change Stative.coord _ (Sieve.widths _ _ 0)=_; rw [map_zero,map_zero]),mul_zero,sub_zero] at h; exact h
         _ = _:=by rw [sum_const,Finset.card_univ, nsmul_eq_mul]; exact (mul_assoc ..).symm
    refine Incidence.spare Θ Va A' Xb q' P₂ R₁ hTT rfl rfl Vp Rt Jt Jx (hm.symm ▸ tower_inj L' d K H G U Γ (Qx) Tq Oq A Qe φ X hM) T P g0 hp' (fun i=>(hg0 i).sight.travels) (fun i hi=>(hl i hi).1) ?_ (hit_collect (wrap f A) P g0 (fun i=>(hXPub.sailX.anchor _) ▸ (Z.p.addr i).anchor) hQ0) hμ hbA haQ (Kit.slope_pos _).le hv₀ hCB (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (show 0 ≤ relief L'.L τ from (fan_pos ..).le))) hα (fun i hi=>(hl i hi).2) ?_ -- hp.
    · rw [hm]; exact hf
    intro i; rw [hx]; exact scoredE L' d K H G U Γ A A' Z Oq Qe φ X hM F' hSup hB hR Θ F₁ hO₁ hO G' hWorks hSeat htV hΔ hξ hOc hK hw hX hpF hv1 ha hη hn hN hJ hY hvDx hYt hKΓ hZA hy hnL hDg htQ htY hΩ heB hBV hL hPV hD hCB hμ hs hv Bq i -- order check
end Drawing
end YM.MassiveQCD.Lyre
#print axioms YM.MassiveQCD.Lyre.Drawing.funds
