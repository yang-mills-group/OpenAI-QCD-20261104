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
lemma tiller {D:ι→Support c}{f:ι→ℝ}{E:Gem c N ι} (h:Hit D n f A b)(hz:0≤f)(hc:∀ i,(E.addr i).site ∈ D i)(hr:∀ i, (coverNumber n (E.addr i).support:ℝ) ≤ σ*coverNumber n (D i))(ha:0≤t)(he:t*σ ≤A): Valued E.addr t f n b:=by
     intro i; refine budget_mono (h i) (fun j=>ite_nonneg (mul_nonneg (hz j) (Real.exp_pos _).le) le_rfl) fun j=>?_; by_cases hv: (E.addr j).site=i
     · dsimp only; rw [if_pos hv,if_pos (hv ▸ hc _)]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (hz _)
       exact (mul_le_mul_of_nonneg_left (hr j) ha).trans ((mul_assoc ..).symm.trans_le (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _)))
     exact (if_neg (show (E.addr j).site ≠ i from hv)).le.trans ((h i).1 _)
lemma wire {J:Type}(U:J→RegularAddress c)(P':ι→Prop)(f:ι→ℝ)(g:{i//P' i}→J)(h:Injective g)(G:ι→RegularAddress c)(hp:∀ i:{i//P' i},G i.val=U (g i))(H:J→ℝ)(ht:Valued U t H n b)(he:∀ i, f i= if h:P' i then H (g ⟨i,h⟩) else 0) : Valued G t f n b:=by
    apply Warmlet.answer P' (fun i=>H (g i)) ?_ (fun i h=> by rw [he i,dif_neg h]) (fun i=> by rw [he i,dif_pos i.prop]); intro i
    convert budget_pull g h (ht i) using 2 with j; dsimp only; simp only [hp] -- warning instance
open Villa King

variable {I' V':Type}
noncomputable def jewel (X:I'→ Prop)(g:{i//X i}→ RegularAddress c)(Ω:Gem c N I'):Gem c N I':=⟨fun i=>if h:X i then g ⟨i,h⟩ else Ω.addr i,(Moss.muteK Ω X).view⟩
lemma surfs (X:I'→Prop)(f:{i//X i}→V')(g:V'→RegularAddress c)(Ω:Gem c N I') (h:Injective f) (H:V'→ℝ)(hv:Valued g A H O.B b)(he:∀ i:{i//X i}, let z:=g (f i); Woven z.site z.support O t (Ω.view i.val) (H (f i))): Licence O A b t (Warmlet.jewel X (g∘f) Ω):=by
    let S':= Warmlet.jewel X (g∘f) Ω; let w i:= if h:X i then H (f ⟨i,h⟩) else 0; have hR (i:{i//X i}): S'.addr i.val=g (f i):=dif_pos i.property
    refine ⟨w,wire _ X _ f h S'.addr hR H hv (fun _=>rfl),fun i=>?_⟩
    change Woven (S'.addr i).site _ _ _ ((Moss.muteK _ _).view i) _; rw [eitherX]; split
    next hh=> let x: {i//X i}:=⟨i,hh⟩; rw [show (S'.addr i)=g (f x) from hR x,show w i=_ from dif_pos hh]; exact he x
    next hh=> rw [show w i=0 from dif_neg hh]; exact freeK ..
lemma yachts (B D: Gem c N I') (hp:D.view=B.view)(ht:Licence O t' a t D) (f:I'→ℝ) (hv:∀ i, Woven (B.addr i).site (B.addr i).support O t (B.view i) (f i))(hU:Hit (fun i=>(B.addr i).support) O.B f σ b) (hh:(A+1+1)*(frostQ n) ≤ σ)(he:Dyed B)(hG:∀ i,(D.addr i).site∈(B.addr i).support ∧ (B.addr i).support⊆(D.addr i).support ∧ (D.addr i).support⊆ halo (n*O.B) (B.addr i).support) (hr:0≤A)(hz:1 ≤ t)(hm:0 ≤ t') : PayC D (Warmlet.lira B D O.threshold) O t t' A a (payment 1 (4*O.B+2) 0 1 1 b A 0) 0 (Stem.income B O.threshold):=by
    have hf i:0≤ f i:=(hv i).travel; have h:Licence O σ b t B:= ⟨_,anchorM _ _ hf hU,hv⟩; refine coinQ B D h he ht hp.symm (quills _ _ h he hp.symm (Entr.Licence_g ht) (zero_lt_one.trans_le hz) (fun i=>(hG i).1) (fun i=>(hG i).2.1) f ?_ ?_ hr) hz ((mul_nonneg (by linarith) (Nat.cast_nonneg _)).trans hh) hm hr
    · refine tiller (E:=D) hU hf (fun i=>(hG i).1) ?_ (by linarith) hh; intro i; rw [mul_comm]; exact_mod_cast (show coverNumber O.B _ ≤ coverNumber O.B (B.addr i).support*frostQ n from (Corona.cover_mono (hG i).2.2 O.B).trans (touring _ n _ O.B O.B_pos le_rfl))
    intro i U; by_cases he:Healthy O.threshold (B.addr i).support U; · unfold letters; rw [masked_eq _ _ _ _ he]; exact (opticX _ _ _ (zero_lt_one.trans_le hz)).trans ((hv i).sizeU _ he)
    rw [letters,masked_ne _ _ _ _ he,map_zero,norm_zero]; exact hf _
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
lemma favors (j:U₀) (hp:Q₀ j): ∃ i:A₀,j=individual i.code:=by
    obtain ⟨c,i,hp,h⟩:=hp; exact ⟨Warmlet.mk i c h,hp⟩
noncomputable def scribe (i:{j:U₀// Q₀ j}):A₀:= Classical.choose (favors G H' O₀ Gz H Y' Ξ Γ i.val i.property)
local notation "l⁔"=> scribe G H' O₀ Gz H Y' Ξ Γ
lemma whisper (i:{j:U₀//Q₀ j}) : i.val= individual ((l⁔) i).code:= Classical.choose_spec (favors G H' O₀ Gz H Y' Ξ Γ i.val i.property)
lemma twig: Function.Injective l⁔:=by intro i j he; exact Subtype.ext ((whisper G H' O₀ Gz H Y' Ξ Γ i).trans ((congr_arg (fun i:A₀=>individual i.code) he).trans (whisper G H' O₀ Gz H Y' Ξ Γ j).symm))
local notation "R'"=>trunkP H (R⁔) (G!) Y' U
variable (χ:Chi)

-- subst address.R'. via Existential generic.P no bizarre Defeq across Mats. 
set_option maxHeartbeats 400000 in
lemma tolls (hp: Aspen G H' O₀ Gz H Y' (R⁔) U χ O t B b)(hb:r≤ B)(ht : Gosh (M₀) χ σ t O.order O.power)(hr:0≤r)(hz:1≤t)(hv: O.B=ζ)(hδ: O.threshold=Pressure.temp s)(hh: (A+1+1)*(frostQ Q.halo)≤ σ)(hA:0≤A)(he: Peace M₀)(Ω: U₀ → RegularAddress c)(hY:∀ i, (Ω i).support=(seatP (M₀).lightF) i) : ∃ (G':Gem c N (U₀)) (H':Ruby.Hue c N (U₀)),PayC G' H' O t r A b (payment 1 (4*O.B+2) 0 1 1 (flowM G.L s) A 0) 0 (Stem.income (muteK (crude (M₀) χ Ω) (ExtraK (I₀) Ξ Γ)) O.threshold):=by
     obtain ⟨g,hg,hH⟩:=hp.openP; let F:= (scribe G H' O₀ Gz H Y' Ξ Γ); let D:= Warmlet.jewel (Q₀) ((R')∘F) (crude (M₀) χ Ω); have hR:=surfs (Q₀) F (R') (crude (M₀) χ Ω) (twig ..) g (show Valued (R') B g O.B b from (by rw [hv]; exact hH)) (O:=O) (t:=t) (fun i=>?_); swap -- B argument mistake
     · let z:=F i; have hz:= hg z Ω; exact (congr_arg (fun i:U₀=>(crude (M₀) χ Ω).view i) (whisper G H' O₀ Gz H Y' Ξ Γ i)).symm ▸ hz
     obtain ⟨f,hp,hx,-⟩:=ht.bills; let Z:=muteK (crude (M₀) χ Ω) (Q₀); have hz' : (fun i=>(Z.addr i).support)=seatP (M₀).lightF:=funext hY
     have hQ (i:U₀) : Woven (Ω i).site (Ω i).support O t (Z.view i) (f i):=by
         rw [hY]; unfold Z; have hh:= hp O Ω hY rfl rfl hv hδ i; rw [Moss.eitherX]; split; exact hh; exact (freeK ..).stretches (Subset.refl _) hh.travel
     refine ⟨D,Warmlet.lira Z D O.threshold,yachts Z D rfl (wells _ hR hb le_rfl) f hQ (hv.symm ▸ (hz'.symm ▸ hx)) hh (dyedM _ (upstream _ Ω χ he) (Q₀)) ?_ hA hz hr⟩; intro i; by_cases he:Q₀ i
     · let v:{i// Q₀ i}:=⟨_,he⟩; let p:=F v; have hR:= groom H (R⁔) (G!) Y' U p; have ht:= (plateK H (R⁔) (G!) Y' U p); have hZ : (Z.addr i).support=past H (R⁔) (G!) Y' p := (hY i).trans ((congr_arg (fun i:U₀=> (seatP (M₀).lightF) i) (whisper G H' O₀ Gz H Y' Ξ Γ v)).trans ((cottage _ _ _ p.earns).1)); rw [show D.addr i=(R') p from dif_pos he,hZ,hv]; exact ⟨hR.1.symm ▸ ht.2.1,hR.2⟩
     rw [show D.addr i=Z.addr i from dif_neg he]; exact ⟨(Ω i).anchor,Subset.refl _,halo_subset ..⟩
end Warmlet
end YM.QCD.Shells
