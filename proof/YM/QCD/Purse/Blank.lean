import YM.QCD.Purse.Board
import YM.QCD.Tax.Glory
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
variable {x:ℝ}
namespace Warmlet
-- abstract match predicate.C.Input. helmets. for dressing. ANY Ω. Integration returns H budget.B file.Depth.a.G.
variable {p':ℕ}
abbrev Graded (f:ι→Prop)(M:ι→RegularAddress c)(p n:ℕ)(b:ι→ℝ)(A v:ℝ):= Anchored (fun i=>(M i).site) (fun i=> if f i then b i else 0) (fun i=>coverNumber p (M i).support) A v
abbrev Valued (X:ι→ RegularAddress c)(v:ℝ)(H:ι→ℝ)(b:ℕ)(c:ℝ):= Anchored (fun i=>(X i).site) H (fun i=>coverNumber b (X i).support) v c
lemma vex (V:ι→RegularAddress c)(Z:ι→ℝ) (hz:Valued V u Z i x):∀ j,0 ≤ Z j:= by
    intro j; let t:=(V j).site; have h:= (hz t).1 j; dsimp only at h; rw [if_pos (show (V j).site=t from rfl)] at h; exact nonneg_of_mul_nonneg_left h (Real.exp_pos _)
lemma advance (V:ι→RegularAddress c)(Z H:ι→ℝ)(hp: Valued V u Z i x)(ht: Valued V u H i y): Valued V u (fun i=> Z i+H i) i (x+y):=by
    intro X; convert budget_plus (hp X) (ht X) using 1; ext i; simp only; split <;> simp [*,add_mul]
-- bundle context
variable {j0 j1 p₀:ℕ}{a₁ b₁ a₂ b₂ m₀ t₀ η₀ :ℝ} (G:Flight n k)(H':f.val=c.val*G.L.val) (O₀:KernelChoices)
local notation "S'"=> G.visit O₀ H'
variable {T:Tube su (G.visit O₀ H')}{P₀:Plan n}{T₁:Garden.Offer 1 a₁ b₁}{T₂:Garden.Offer 2 a₂ b₂}
variable (Gz : Jets.Sun G c f H' t' u q η a l (pesto P₀ G H' (trunkM T₁ T₂ w m₀ f)))
variable (U': Jets.Sun G c f H' t' u q η a l (pesto P₀ G H' (trunkM T₁ T₂ w 0 f)))
variable (H:Cash W s μ L Q o C T (trimP T R δ β B₀))
variable {E J: Type}[Countable E][Countable J]
variable (Y':Rise f N E J) (Y:Fleet H ι N)
variable (U: Cash W s μ L Q o C T (lore (trimP T R δ β B₀)))
local notation "ζ"=> radiusB s
set_option quotPrecheck false
local notation "G!"=> Gz.equip N ζ
local notation "Z!"=> united (deckHue H (Gz.equip N ζ) Y' (roof (Gz.equip N ζ) Y' 30 ζ)) Y
local notation "A⁔"=> Warmlet H Y (Gz.equip N ζ) Y'
local notation "J‴"=> (Z!).Bright
variable (K': Hera.Rights su j) (β':E→ℝ)(κ:J→ℝ)
variable {D:Heir.Record}{ξ g θ α z p' ρ X Λ σ Y₂ V:ℝ}{T':ℝ}(φ ψ A0 :ℝ) (f': Flavor N)
variable (hL:Works P L s (G.visit O₀ H') T)(hO:O.B=radiusB s)(he:News P L s W Q o μ C j N' D χ O.power z p' g (G.visit O₀ H').patch) (hp:Plays N' D O R P T s)
variable (Ω:Clusters (united (deckHue H (Gz.equip N (radiusB s)) Y' (roof (Gz.equip N (radiusB s)) Y' 30 (radiusB s))) Y).Bright → RegularAddress c)
local notation "γ"=>fun i=>Real.exp 1*terra Gz N ζ x y i
local notation "K₀"=> cashM L θ s
variable (hh:Coins O R P L D Q.halo N' K' s β x y t' u η σ q a u z g ρ m₀ p' ξ x θ P₀ N l)
variable (hm:|m₀| ≤haloK L s)(ha: Peak (Gz.equip N (radiusB s)) R.threshold x y ξ fun i=>Real.exp 1*terra Gz N (radiusB s) x y i)(hk:Sea G H' (radiusB s) t' φ q R.threshold Gz.Z Gz.V 2)(hK:0 ≤ φ)(hj:4*(fingers N*φ*y) ≤ x/8)(hu:y*fingers N*q ≤ ξ*x)(hQ:∀ i,terra Gz N (radiusB s) x y i ≤1)
variable (hf:Y'.Wave R.threshold) (hC:Y'.Reframe)(hr:0<η)(hS:Seats H χ)
variable (hY:(united (deckHue H (Gz.equip N (radiusB s)) Y' (roof (Gz.equip N (radiusB s)) Y' 30 (radiusB s))) Y).Famous)(hΨ:Peace (united (deckHue H (Gz.equip N (radiusB s)) Y' (roof (Gz.equip N (radiusB s)) Y' 30 (radiusB s))) Y))
variable (ht:α≤ y)(hz:0<α)(h'h:fareG 1 α N ≤ y)(hn:5 ≤ j)(hΓ':∀ i,Warp G.L i ((sliceL G H').parent i) (ply G H') N x y ψ A0)
variable (hG: ∀ e0:E, Spice.Worth Y' e0 R x (β' e0) ∧(Nonwrapping (Y'.row e0).support (Y'.row e0).site→Feast R (Y'.row e0).support (Y'.row e0).site f' (Y'.main e0) x (β' e0))) (hτ: ∀ i,β' i ≤ chip L s)
local notation "p!"=> paidSet (Gz.equip N ζ) Y' γ β' κ ξ K₀ X 1
variable (hΓ: Trees.Ready (roof (Gz.equip N (radiusB s)) Y' Q.halo (radiusB s)) (radiusB s) (paidSet (Gz.equip N (radiusB s)) Y' (fun i=> Real.exp 1*terra Gz N (radiusB s) x y i) β' κ ξ (cashM L θ s) X 1) A T' 1 V)(hχ:1≤X)(hB:1 ≤ cashM L θ s)(hΩ:Cents Y' β' κ x R.threshold)
-- Stake principal anchored old AND new. many mass. dual use Ω ANY if depends addr? yes.
local notation "o!"=> trunkP H Y (Gz.equip N ζ) Y' U
local notation "t!"=> Small H Y (Gz.equip N ζ) Y'
variable (i':Warmlet H Y (Gz.equip N (radiusB s)) Y')
local notation "A₀"=> perch H Y (Gz.equip N ζ) Y' U
local notation "P⁔"=> prince H Y (Gz.equip N ζ) Y'
local notation "W?"=> wageP H Y (Gz.equip N ζ) Y' U K₀ (caseT N' K' O L s) (p!)
local notation "V?"=> Warmlet.petty H Y (Gz.equip N ζ) Y' U N' K' O A0 β'
include U' hL hO he hp hh hm ha hk hK hj hu hQ hf hC hr hS hY hΨ ht hz h'h hn hΓ' hG hτ hΓ hχ hB hΩ
set_option maxRecDepth 3000 in
set_option maxHeartbeats 800000 in
lemma farmP (he':Woven ((A₀) i').site ((Z!).fullA i'.code.val) O α ((crude (Z!) χ Ω).view (individual i'.code)) Y₂)(ht':0 ≤ (W?) i'):
    Woven ((o!) i').site ((o!) i').support O α ((crude (Z!) χ Ω).view (individual i'.code)) ((V?) i'+(W?) i'+ if (t!) i' U then 0 else Y₂):=by
   let u:=i'.label.val; let b:=i'.code; have hpK : Aliased (Z!) b (.inl i'.label):=i'.earns
   have hx:= (cottage _ b _ hpK).2
   by_cases hz': (t!) i' U; swap
   · rw [trunkP,if_neg hz', Warmlet.petty, if_neg hz', if_neg hz']; rw [show (W?) i'=0 from if_neg (fun h=> hz' h.1)]; simp only [add_zero,zero_add]; exact he'.stretches (show ((Z!).fullA i'.code.val)⊆(perchS H Y (Gz.equip N ζ) Y' U i').support from le_of_eq hx) le_rfl
   rw [trunkP,if_pos hz',if_pos hz',add_zero]; let P:= Gz.equip N ζ
   obtain ⟨hU,hΦ,-⟩:=Classical.choose_spec (oak H Y P Y' i'); let F:=oath H Y P Y' i'
   have hzO:coverNumber O.B (Brim.plate U F).support ≤ O.B:=hO.symm ▸ hz'
   have hy:=gardens H P Y' i'.label Y (stop H Y P Y' i')
   by_cases heK : P⁔ i'
   · rw [Warmlet.petty,if_pos hz',dif_pos heK]; apply Woven.stretches (A:=_) _ (Subset.refl ((A₀) i').support) (le_add_of_nonneg_right ht')
     let p:Duke H Y P Y':=⟨_,heK⟩; let j':=col H Y P Y' p
     obtain ⟨h1,h2⟩:= (slate _ _ _ _ i' j').mp (duke H Y P Y' p); obtain ⟨hG,hF⟩:= hG j'
     exact fairT _ _ _ _ _ hL hO he hp Ω f' hy hh hm ha hk hK hj hu hQ hf hr hS hpK hY hΨ F ht hz hU hzO he' j' h1 (hΦ _ h1) hG (hτ _) h2 hn (hΓ' _) hF h'h hC U'
   rw [Warmlet.petty,if_pos hz',dif_neg heK,zero_add]
   have hΦ':u.Nonempty:=i'.label.property.1
   have hM:= congr_arg Finset.card (pinch u); unfold pin at hM; rw [card_disjSum,card_disjSum] at hM
   rcases eq_or_ne (leftE u).card 0 with h|h
   · have hh:= darkness (F':=U) (x₂:=α) (N':=N') (D₀:=g) _ Y' P u hy F χ O D hΦ' (Finset.card_eq_zero.mp h)
     obtain ⟨_,_,_,_,_,_,_,_,_,Ψ,hh',h0⟩:=hS; apply fundsL _ hL he hp hO _ _ (grill _ Y' hy hU) Ω hh' h0 hY hΨ _ hpK Y₂ he' hzO hh le_rfl le_rfl le_rfl ht'; simp only [Hera.lyreFee,Hera.ripple,mul_zero,zero_mul,add_zero]; exact ht'
   by_cases hxB:2 ≤ (leftE u).card
   · have h := manyK _ Y' _ _ _ hL hO he hp Ω β' κ hy hh ha hf hS hpK hY hΨ F ht hz hU hzO he' hΓ hχ hB hΩ hxB
     rw [wageP,if_pos ⟨hz',by change 2 ≤ u.card; omega⟩]; exact h
   obtain ⟨J,hJ⟩:= Finset.card_eq_one.mp (show (leftE u).card=1 by omega)
   have hxA: ops u≠ ∅:= fun h=> heK ⟨_, (slate _ _ _ _ _ J).mpr ⟨hJ,h⟩⟩
   rw [wageP,if_pos ⟨hz', show 2≤ u.card from by have h₀:=Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hxA); omega⟩]
   exact someK _ _ _ _ _ hL hO he hp Ω β' κ hy hh hm ha hk hK hj hu hQ hf hr hS hpK hY hΨ F ht hz hU hzO he' _ hJ (hΦ _ hJ) (hG _).1 (hτ _) hΓ hχ hB hΩ hxA le_rfl
end Warmlet
end YM.QCD.Shells
