import YM.QCD.Purse.Haven
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Entrance
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
-- Anchor dictionary only needs single B. Y estimator equality of register. 
variable {E J: Type}[Countable E][Countable J]{D:Type}[Fintype D]
variable (H) (P': Send S.ratio N D) (Y':Rise f N E J)
local notation "L₀"=> P'
set_option quotPrecheck false
local notation "K₀"=> Wound (roof P' Y' 30 (radiusB s))
local notation "ζ"=> radiusB s
local notation "Y!"=> deckHue H P' Y' (roof P' Y' 30 ζ)
local notation "Z!"=> united (Y!) Y
local notation "A⁔"=> Warmlet H Y P' Y'
namespace Warmlet
local notation "Tz"=> (lore (trimP T R δ β B₀))
variable (p : Warmlet H Y P' Y')
noncomputable def oath :ℕ:= Classical.choose (oak H Y P' Y' p)
abbrev boon (p: Warmlet H Y P' Y') : Finset (Fj D E J):= p.label.val
variable (V:Cash W s μ L Q o C T (lore (trimP T R δ β B₀)))
noncomputable def perch (p: Warmlet H Y P' Y'):= Brim.plate V (oath H Y P' Y' p)
-- Lean order. Old anchor custom p. site ok always. Llize.
lemma plateK (p:Warmlet H Y P' Y'): (perch H Y P' Y' V p).support=p.label.val.biUnion (roof P' Y' Q.halo ζ) ∧ (perch H Y P' Y' V p).site∈ past H Y P' Y' p ∧ ∀ i:E,leftE p.label.val={i}→(perch H Y P' Y' V p).site=S.ratio.parent (Y'.row i).site:=by
    obtain ⟨hx,ht,hp⟩:=Classical.choose_spec (oak H Y P' Y' p)
    refine ⟨?_,hp,fun i hi=> congr_arg S.ratio.parent (ht _ hi)⟩ -- congr parent
    unfold perch; change Footprint.enlargement S.ratio _ _ (inspected _)=_; rw [oath,hx]; exact brink ..
lemma sky (i:Fj D E J): roof P' Y' 30 ζ i ⊆ roof P' Y' Q.halo ζ i := Corona.halo_mono (Nat.mul_le_mul_right _ (by linarith [Q.buys])) (Subset.refl _)
noncomputable def perchS (p:Warmlet H Y P' Y'): RegularAddress c:=⟨(perch H Y P' Y' V p).site,p.label.val.biUnion (roof P' Y' 30 ζ), (plateK H Y P' Y' V p).2.1⟩
abbrev Small (p:Warmlet H Y P' Y') (V:Cash W s μ L Q o C T (lore (trimP T R δ β B₀))) :Prop:= coverNumber ζ (perch H Y P' Y' V p).support ≤ ζ
noncomputable def trunkP (p:Warmlet H Y P' Y'):RegularAddress c:= if Small H Y P' Y' p V then perch H Y P' Y' V p else perchS H Y P' Y' V p -- order likely V p -> inspect small explicit order.
lemma groom (p:Warmlet H Y P' Y'): let b:= trunkP H Y P' Y' V p
    let x:= past H Y P' Y' p;b.site=(perch H Y P' Y' V p).site ∧ x⊆ b.support∧ b.support⊆ halo (Q.halo * ζ) x:=by
    intro b x; unfold b trunkP; split
    · rw [ (plateK H Y P' Y' V p).1]; refine ⟨rfl,?_,stretchP H Y P' Y' p⟩
      apply biUnion_mono; exact fun i _=>sky _ _ i -- lemma
    exact ⟨rfl,Subset.refl _,halo_subset ..⟩
-- Principal cost pre.Coarse.
def prince (p:Warmlet H Y P' Y'):Prop := ∃ i:E, p.label.val = {Sum.inr (.inl i)}
lemma slate (p:Warmlet H Y P' Y') (e:E): p.label.val={Sum.inr (.inl e)} ↔ leftE p.label.val={e}∧ ops p.label.val=∅:=by
    constructor
    · intro h; rw [h]; refine ⟨?_,?_⟩
      · apply Finset.ext; simp [leftE]
      apply Finset.ext; simp [ops]
    rintro ⟨hx,hz⟩; nth_rw 1 [←pinch p.label.val]; rw [hx,hz, stop H Y P' Y' p]; unfold pin; apply Finset.ext; rintro (i|i|i)<;>simp
abbrev Duke := {p:Warmlet H Y P' Y' // Warmlet.prince H Y P' Y' p}
noncomputable def col (p: Duke H Y P' Y'):= Classical.choose p.property
@[simp] lemma duke (p:Duke H Y P' Y'): p.val.label.val={Sum.inr (.inl (col H Y P' Y' p))}:= Classical.choose_spec p.property
lemma copyL : Function.Injective (col H Y P' Y'):= fun i j hx=>Subtype.ext (iden _ _ _ _ i.val j.val (by rw [duke H Y P' Y',duke H Y P' Y',hx]))
lemma sizeP (p:Duke H Y P' Y')(hp:P'.trim+1 ≤ R.B + R.B) : coverNumber R.B (brimW P' Y' p.val.label.val) ≤ coverNumber R.B (Y'.row (col H Y P' Y' p)).support * 9^4:=by
    unfold brimW; rw [duke H Y P' Y',singleton_biUnion]; exact miles _ _ _ R.B_pos hp
lemma terrestrial (p:Duke H Y P' Y')(hp:P'.trim≤ ζ)(hv:R.B ≤ 2*ζ)(hz:0 < ζ): (coverNumber ζ (perch H Y P' Y' V p.val).support:ℝ) ≤ preCost (Q.halo+8)+conversion S.ratio (Q.halo+8)*coverNumber R.B (Y'.row (col H Y P' Y' p)).support:=by
    let i:=col H Y P' Y' p; let X:=(Y'.row i).support
    have hh:(perch H Y P' Y' V p.val).support⊆ Footprint.enlargement S.ratio (Q.halo+8) ζ X:=by rw [ (plateK H Y P' Y' V p.val).1,duke H Y P' Y',singleton_biUnion]; exact (roofs P' Y' _ _ hp hz).2 _
    exact (Nat.cast_le.mpr (Corona.cover_mono hh _)).trans (footprint _ _ _ _ X hz hv) -- syntax ..
-- Principals budget over Duke. later joins incl size=1 left≠ Hue.K Omega.Drawing.
variable (K': Hera.Rights su j)
noncomputable def doll (O:BudgetPoint) (Z:Libretto su j)(K':Hera.Rights su j)(v:ℝ)(z:E→ℝ)(p:Duke H Y P' Y'):=fern L^5*z (col H Y P' Y' p)*fluteT Z K' O v (coverNumber R.B (brimW P' Y' p.val.label.val))
variable (β':E→ℝ) {ε ψ X v₁:ℝ}
lemma bornZ (hp:P'.trim+1≤ R.B+R.B)(hX:0≤β')(hd:Capstone L (Q.halo+8) O.power A B ε N' K' ψ)(hv:R.B≤ 2*ζ)(he:P'.trim≤ζ)(hz:0<ζ)(hε:0 ≤ε)(hh:Anchored (fun i=>(Y'.row i).site) β' (fun i=>coverNumber R.B (Y'.row i).support) A v₁):
    Anchored (fun i:Duke H Y P' Y'=> (perch H Y P' Y' V i.val).site) (doll H Y P' Y' O N' K' ψ β') (fun p=> coverNumber ζ (perch H Y P' Y' V p.val).support) B (ε*v₁):=by
    let d:=col H Y P' Y'; let t p:=coverNumber R.B (Y'.row (d p)).support; let v (p : Duke H Y P' Y'):=coverNumber ζ (perch H Y P' Y' V p.val).support; let o' i:=(Y'.row i).site; let P₁:=doll H Y P' Y' O N' K' ψ β'; have hD : S.ratio.count=L:= H.laws.data.funds.length_eq
    let L':ℝ:=(L.val:ℝ)^4; have hp':0<L':=by unfold L'; positivity
    let D p:=P₁ p*Real.exp (B*v p); have ht(p):0 ≤ P₁ p:=mul_nonneg (mul_nonneg (pow_nonneg (fern_pos _).le _) (hX _)) ((by norm_num : (0:ℝ) ≤2).trans (alertF ..|>.2)); have hnn p:0 ≤ D p:=mul_nonneg (ht p) (Real.exp_pos _).le
    have hΦ (p:Duke H Y P' Y'): (perch H Y P' Y' V p.val).site= S.ratio.parent (o' (d p)):= (plateK H Y P' Y' V p.val).2.2 _ ((slate _ _ _ _ _ _).mp (duke H Y P' Y' p)).1
    have hr(p): D p ≤ L'⁻¹*ε * (β' (d p)*Real.exp (A*t p)):=by
        rw [show L'⁻¹*_ * _= ε*(β' (d p)*Real.exp (A*t p))/L' from by ring]
        apply (le_div_iff₀ hp').mpr; have hQ:= hd.lots O rfl c f S.ratio hD (v p) _ _ (sizeP H Y P' Y' p hp) (terrestrial H Y P' Y' V p he hv hz)
        let i:= col H Y P' Y' p; unfold D P₁ doll; calc
           _ = β' i*(fern L^5 * fluteT N' K' O ψ (coverNumber R.B (brimW P' Y' p.val.label.val))* Real.exp (B*(v p))*L'):=by unfold i; ring
           _ ≤ _:= (mul_le_mul_of_nonneg_left hQ (hX _)).trans_eq (by unfold t; change _= ε*(β' i*Real.exp _); ring)
    have hF(x):SumBudget (fun i:Duke H Y P' Y'=> if o' (d i)=x then D i else 0) ((L'⁻¹*ε)*v₁):=by
       refine budget_mono (budget_scale (mul_nonneg (inv_pos.mpr hp').le hε) (budget_pull d (copyL ..) (hh x))) (fun i=> ite_nonneg (hnn i) le_rfl) fun i=> ?_
       change (if o' _=_ then _ else _) ≤ _*(if o' _=x then _ else _)
       split
       next heB=> exact hr i
       next h=> rw [mul_zero]
    intro x; simp_rw [hΦ]; rw [show ε*v₁=(S.ratio.count.val:ℝ)^4*(L'⁻¹*ε*v₁) from by rw [hD]; change _= L'*_; field_simp]; exact dense S.ratio (o' ∘ d) D _ hnn hF x
end Warmlet
end YM.QCD.Shells
