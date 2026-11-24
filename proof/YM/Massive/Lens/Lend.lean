import YM.Massive.Lens.Width
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
variable (hB :Boost G H' O₀ Gz H Y' (R⁔) N' K₂ V' β' K₀ U χ O t B b)
variable (hC:Capstone G.L (Q.halo+8) O.power uF B (A3*fern G.L) N' K₂ V')
-- avoid definitional tactic on RHS for `Support`: Bigger
structure Bigger {c:Side}{I:Type}(E D:Gem c N I)(n:ℕ) :Prop where
   view : D.view=E.view
   bump (i:I): (D.addr i).site∈(E.addr i).support ∧ (E.addr i).support⊆(D.addr i).support ∧ (D.addr i).support⊆ halo n (E.addr i).support
set_option maxHeartbeats 850000 in
lemma stroll (hp:Boost G H' O₀ Gz H Y' (R⁔) N' K₂ V' β' K₀ U χ O t B b)(ht : Gosh (M₀) χ σ t O.order O.power)(hv: O.B=ζ)(hδ: O.threshold=Pressure.temp s)(Ω: U₀ → RegularAddress c)(hY:∀ i, (Ω i).support=(seatP (M₀).lightF) i) (hQ:0≤β')(hM:Capstone G.L (Q.halo+8) O.power uF B (A3*fern G.L) N' K₂ V') (he:A3≥0)(hJ:ζ+1≤R.B+R.B)(hR:R.B≤2*ζ)(hS:B ≤ σ):
      ∃ F:Gem c N (U₀), Bigger (crude (M₀) χ Ω) F (Q.halo*O.B) ∧∀ (X: U₀ → Prop)(w:E→Prop)(u:ℝ), (∀ p:Duke H (R⁔) (G!) Y',X (individual p.val.code)→w (col H (R⁔) (G!) Y' p))→(∀ i,X i→ stand (M₀) nectarP i) → Valued Y'.row uF (fun i=> if w i then inflate3 G.L K₀ β' i else 0) R.B u → Licence O B (jelly G.L s+(A3*fern G.L*u+b)) t (muteK F X):=by
     obtain ⟨p,hA,h⟩:=hp.toBank3.price
     let w₁:= A3*fern G.L; let Z:= crude (M₀) χ Ω; let S(i :{i:U₀//Q₀ i}) := scribe G H' O₀ Gz H Y' Ξ Γ i; let W:=Warmlet.jewel (Q₀) ((R')∘S) Z; let F:Gem c N U₀:= ⟨W.addr,Z.view⟩; have hΨ (i:{i:U₀//Q₀ i}) : F.addr i.val= (R') (S i):= dif_pos i.property
     have hx(i)(h:¬ Q₀ i): F.addr i=Z.addr i:=dif_neg h;
     refine ⟨F,⟨rfl,fun i=>?_⟩,?_⟩
     · by_cases he:Q₀ i
       · let y:{i:U₀//Q₀ i}:=⟨i,he⟩; let z:=S y; have hr:= groom H (R⁔) (G!) Y' U z; have hj:= plateK H (R⁔) (G!) Y' U z; have hE : (Z.addr i).support=past H (R⁔) (G!) Y' z:= (hY i).trans ((congr_arg (fun i:U₀=> (seatP (M₀).lightF) i) (whisper G H' O₀ Gz H Y' Ξ Γ y)).trans ((cottage _ _ _ z.earns).1)); rw [show F.addr i=(R') z from hΨ y,hE,hv]; exact ⟨hr.1.symm ▸ hj.2.1,hr.2⟩
       rw [hx i he]; exact ⟨(Z.addr i).anchor,Subset.refl _,halo_subset ..⟩
     intro T w u hT hT' hr
     obtain ⟨f,hP,h',hf⟩:= ht.bills
     let d₀:= Dated (M₀) Fury nectarP s; let f₀ i:= if d₀ i then f i else 0
     let ℓ:=jelly G.L s; let T₁ (i:U₀):= T i∧¬ Q₀ i; let T₂ (i:U₀):= T i∧ Q₀ i
     have hz : Valued Z.addr σ f₀ O.B ℓ:= by
         have hneg(i):0 ≤ f i :=(hP O Ω hY rfl rfl hv hδ i).travel; have heq:(fun i=>(Z.addr i).support)=(seatP (M₀).lightF):=funext hY; refine anchorM Z _ (fun i=>ite_nonneg (hneg _) le_rfl) ?_; rw [heq,hv]; exact hf
     have he' : Licence O B ℓ t (muteK F T₁):= wells _ (chargedWidth Z F (Q₀) T hx rfl f₀ (fun i hi hk=>?_) hz) hS le_rfl;
     swap
     · have hx := sectorCut H (R⁔) (G!) Y' i hk (hT' i hi); rw [show f₀ i=f i from if_pos hx]; exact (hY i).symm ▸ (hP O Ω hY rfl rfl hv hδ i)
     let T₃(i:A₀):=T (individual i.code)
     let g₀ := Warmlet.petty H (R⁔) (G!) Y' U N' K₂ O V' (inflate3 G.L K₀ β'); let g(i:A₀):= if T₃ i then g₀ i else 0
     have hε: Valued (R') B g O.B (w₁*u):= by rw [hv]; exact poor H (R⁔) (G!) Y' U K₂ (inflate3 G.L K₀ β') V' T₃ w u hM (mul_nonneg he (fern_pos G.L).le) (fun i=>inflate_nil _ _ _ i (hQ i)) hJ le_rfl (hv ▸ O.B_pos) hR hT hr
     have hp₂: Licence O B (w₁*u+b) t (muteK F T₂):=by
         have hm := valued_sum (R') g p hε (show Valued (R') B p O.B b from hv.symm ▸ h)
         refine lendWidth Z F (Q₀) T (R') S (twig ..) hΨ rfl (g+p) hm (fun i hi=>?_); let p':=S i; have hw:i.val=individual p'.code:= whisper G H' O₀ Gz H Y' Ξ Γ i; have hh: T (individual p'.code):= hw ▸ hi; rw [Pi.add_apply,show g (S i)=_ from if_pos hh]; exact (congr_arg Z.view hw).symm ▸ (hA p' Ω)
     exact costUnion F T₁ T₂ T he' hp₂ (fun i hi=> by by_cases he:Q₀ i; exact Or.inr ⟨hi,he⟩; exact Or.inl ⟨hi,he⟩)
end Warmlet
end YM.QCD.Shells
#print axioms YM.QCD.Shells.Warmlet.stroll
