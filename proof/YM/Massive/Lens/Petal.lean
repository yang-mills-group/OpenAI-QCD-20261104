import YM.Massive.Lens.Lily
import YM.Massive.Pith.Bill
import YM.Massive.Struck.Inherit
import YM.QCD.Finch.Tissues
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
open Trees Ac Further.ShellBirth49.Fusing Collide
open Labels
variable {p i j' m m':ℕ}
namespace Warmlet
variable {β':ℝ}{t₅ p':ℝ}{θ σ:ℝ}
open Finch Stem Grove Moss Calm
open Villa King
open YM.QCD.Loom.Fleet Struck
-- departure stage in G.Coordinates
variable {j0 j1 p₀:ℕ}{a₁ b₁ a₂ b₂ m₀ t₀ η₀ :ℝ} (G:Flight n k)(H':f.val=c.val*G.L.val) (O₀:KernelChoices)
local notation "S'"=> G.visit O₀ H'
variable {T:Tube su (G.visit O₀ H')}{P₀:Plan n}{T₁:Garden.Offer 1 a₁ b₁}{T₂:Garden.Offer 2 a₂ b₂}
variable (Gz : Jets.Sun G c f H' t' u q η a l (pesto P₀ G H' (trunkM T₁ T₂ w m₀ f)))
variable (H:Cash W s μ G.L Q o C T (trimP T R δ β B₀))
variable {E J: Type}[Countable E][Countable J]
variable (Y':Rise f N E J) (U: Cash W s μ G.L Q o C T (lore (trimP T R δ β B₀)))
variable  {G' : St f}{X₀:ℕ→Atom su 2}{P':Plan k}{J' K' ε' τ:ℝ}(Ξ: Swathe G H' G' X₀ P' d C' J' K' ε' m)(Γ:Land c (Site c) (Site c))
local notation "ζ"=> radiusB s
set_option quotPrecheck false
local notation "G!"=> Gz.equip N ζ
local notation "R⁔"=> united (VarnC H Ξ N) (sailP H Γ N)
local notation "I₀"=> deckHue H (Gz.equip N ζ) Y' (roof (Gz.equip N ζ) Y' 30 ζ)
local notation "M₀"=> artV (deckHue H (Gz.equip N ζ) Y' (roof (Gz.equip N ζ) Y' 30 ζ)) Ξ Γ
local notation "U₀" => Clusters (M₀).Bright
local notation "Q₀" => ExtraK (I₀) Ξ Γ
local notation "A₀"=> Warmlet H (R⁔) (G!) Y'
local notation "R'"=>trunkP H (R⁔) (G!) Y' U
variable (χ:Chi)

-- subst address.R'. via Existential generic.P no bizarre Defeq across Mats. 
variable (K₂: Hera.Rights su j0)(N':Libretto su j0)(A3 V':ℝ)(β':E→ℝ)(K₀:E→Bool) {uF:ℝ}
local notation "C₀"=> Duke H (R⁔) (G!) Y'
local notation "Q⁺"=> chosen G H' O₀ Gz H Y' Ξ Γ
local notation "E⁺"=> horizonKey G H' O₀ Gz H Y' Ξ Γ
local notation "D'"=> col H (R⁔) (G!) Y'

variable (E' : E→ Dye)(J₁ : J→ Dye)
local notation "Dv"=> wages G H' O₀ Gz H Y' Ξ Γ E' J₁
noncomputable def riseP (Y': Rise f N E J)(W:Site f×Flavor N→E) : Site f×Flavor N → Clusters (artV (deckHue H (Gz.equip N ζ) Y' (roof (Gz.equip N ζ) Y' 30 ζ)) Ξ Γ).Bright:= horizonKey G H' O₀ Gz H Y' Ξ Γ ∘ W
variable (W₀:Site f × Flavor N→E)(T1 T2 T3:E→Prop) -- addr
local notation "G⁺"=> riseP G H' O₀ Gz H Ξ Γ Y' W₀ -- order check
lemma profitE (x:E): Dv (E⁺ x)=E' x:= (horizonPay G H' O₀ Gz H Y' Ξ Γ E' J₁ ((address H (R⁔) (G!) Y').symm x)).trans (congr_arg E' (key_coded ..))

-- payments.exp witness. all needed: for each flavor HR.B origin M.E.Act. 
variable {y' A' epsilon MS LS HS:ℝ} (mχ:Flavor N→ℝ)
lemma massBoost (hp:Boost G H' O₀ Gz H Y' (R⁔) N' K₂ V' β' K₀ U χ O t B b)(h0:∀ i,coverNumber R.B (Y'.row (W₀ i)).support ≤1 ∧ ∀ x,Y'.main (W₀ i) x=Y'.main (W₀ i) 1)(a:Flavor N)(i:Site f×Flavor N)(Ω: U₀→ RegularAddress c)(ht:0<t) : ‖watchW c t a ((crude (M₀) χ Ω).view (G⁺ i) 1)- planeW c t a (Dust.bill (proton G H') N (Y'.main (W₀ i) 1))‖ ≤2*(fern G.L ^5*β' (W₀ i)):=by
     let J:= (address H (R⁔) (G!) Y').symm (W₀ i); let R:=proton G H'; have hr:D' J=W₀ i:=key_coded ..; rw [← hr]; -- LHS occurrence? inside G⁺ i too not syntactically. good.
     apply hp.flatRange J ?_ (fun x=>?_) Ω (planeW c t a) (allegiance _ a ht.le); · rw [hr]; exact (h0 i).1
     rw [hr]; exact (h0 i).2 x
lemma proceeds (hp:Boost G H' O₀ Gz H Y' (R⁔) N' K₂ V' β' K₀ U χ O t B b)(ht : Gosh (M₀) χ σ t O.order O.power)(hv: O.B=ζ)(hδ: O.threshold=Pressure.temp s)(Ω: U₀ → RegularAddress c)(hY:∀ i, (Ω i).support=(seatP (M₀).lightF) i) (hQ:0≤β')(hM:Capstone G.L (Q.halo+8) O.power uF B (A3*fern G.L) N' K₂ V')(he:A3≥0)(hJ:ζ+1≤R.B+R.B)(hR:R.B≤2*ζ)(hS:B ≤ σ) (he':∀ i, (E' (W₀ i)).1=1)(hT1:∀ i,T1 (W₀ i))(hT2:∀ i,(E' i).1=1→ i∉Set.range W₀→ T2 i)(hT3:∀ i,2≤ (E' i).1→ T3 i)(hsX:Valued Y'.row uF (fun i=>if T1 i then inflate3 G.L K₀ β' i else 0) R.B MS)(hsY:Valued Y'.row uF (fun i=>if T2 i then inflate3 G.L K₀ β' i else 0) R.B LS)(hsR:Valued Y'.row uF (fun i=>if T3 i then inflate3 G.L K₀ β' i else 0) R.B HS):
      let u(v:ℝ):= jelly G.L s+(A3*fern G.L*v+b); let Qμ:=G⁺; ∃ F:Gem c N U₀, Bigger (crude (M₀) χ Ω) F (Q.halo*O.B) ∧ Licence O B (u MS) t (muteK F fun i=> i∈Set.range Qμ)∧ Licence O B (u LS) t (muteK F (fun i=> (Dv i).1=1∧ i∉Set.range Qμ)) ∧ Licence O B (u MS+u LS) t (muteK F fun i=>(Dv i).1=1)∧ Licence O B (u HS) t (muteK F fun i=>2 ≤ (Dv i).1):=by
     intro u Z; obtain ⟨D,hD,h⟩:= stroll G H' O₀ Gz H Y' U Ξ Γ χ K₂ N' A3 V' β' K₀ hp ht hv hδ Ω hY hQ hM he hJ hR hS
     let f₀ i:= i∈ Set.range Z; let hχ(i:U₀):=(Dv i).1=1; let f₁ i:=hχ i∧¬ f₀ i; have hδ'(i:U₀)(hx:hχ i):= shadowed G H' O₀ Gz H Y' Ξ Γ E' J₁ i (hx.trans_ne Nat.one_ne_zero)
     have hP0 := h f₀ T1 MS (fun i hi=> ?_) (fun i hi=>?_) hsX
     rotate_left
     · obtain ⟨j,hx⟩:=hi; change E⁺ (W₀ j)=Q⁺ i at hx; exact (key_copy G H' O₀ Gz H Y' Ξ Γ _ _ (hx.trans (keyed G H' O₀ Gz H Y' Ξ Γ i).symm)) ▸ hT1 j
     · obtain ⟨j,rfl⟩:=hi; apply hδ'; change (Dv (E⁺ (W₀ j))).1=1; rw [profitE]; exact he' j
     have hP1 := h f₁ T2 LS (fun i hi=> ?_ ) (fun i hi=> hδ' i hi.1) hsY
     rotate_left
     · obtain ⟨hd,he⟩:=hi; apply hT2; · unfold hχ at hd; rwa [show Dv (individual i.val.code)= _ from horizonPay G H' O₀ Gz H Y' Ξ Γ E' J₁ i] at hd
       rintro ⟨j,h⟩; exact he ⟨j, (congr_arg (E⁺) h).trans (keyed G H' O₀ Gz H Y' Ξ Γ i)⟩
     refine ⟨D,hD,hP0,hP1,costUnion D f₀ f₁ hχ hP0 hP1 (fun i hi=> by by_cases he:f₀ i; exact Or.inl he; exact Or.inr ⟨hi,he⟩), h _ T3 HS (fun i hi=> ?_) (fun i hi=> shadowed G H' O₀ Gz H Y' Ξ Γ E' J₁ i (Nat.ne_of_gt ((by norm_num :0<2).trans_le hi))) hsR⟩
     apply hT3; rw [← horizonPay G H' O₀ Gz H Y' Ξ Γ E' J₁ i]; exact hi
end Warmlet
end YM.QCD.Shells
#print axioms YM.QCD.Shells.Warmlet.proceeds
