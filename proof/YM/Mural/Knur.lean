import YM.Mural.Tartan
import YM.Mural.Brook
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG
open Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open YM.Next.Free
variable {c f:Side}{j k m:ℕ}
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG
set_option quotPrecheck false
variable (L':Flight j k)(d:f.val=c.val*L'.L.val)(K:KernelChoices)
local notation "L"=> L'.L
local notation "S"=> L'.visit K d
local notation "Ψ"=> sliceL L' d
local notation "M"=> arctic L j
variable {T: Tube su (L'.visit K d)}{T':Teller su}{Q:Target su T'}{v x₀ W μ C:ℝ} {o:Target.Order su W}
variable (x y: Site c)(p q:Site f){N:ℕ}
local notation "Tx"=> texel L' d 0 x p
local notation "Ty"=> texel L' d 0 y q
local notation "Cq"=> cleared p q L' d x y
local notation "Lq"=> loaded p q L' d x y
local notation "Q0"=> (sliceL L' d).embed x
local notation "Yg"=> (sliceL L' d).embed y
local notation "B"=> radiusB x₀
local notation "A₀"=> Lattice.halo B {Q0}
local notation "σt"=> berthD j
variable (hv:separation ((sliceL L' d).embed x) p ≤ arctic L'.L j)(hw:separation ((sliceL L' d).embed y) q ≤ arctic L'.L j)
variable (hp:separation p q≤ berthD j)
variable (hS: (berthD j)*L'.L.val +arctic L'.L j+4*(berthD j)≤ radiusB x₀)
open MassiveQCD MassiveQCD.Plate MassiveQCD.PaletteT QCD.Mural
open MassiveQCD.Apron.Grove Loom Glow
variable {s t p' t₁ t₂ δ β b a y₀:ℝ} {P':Plan k}{X:Run.St f}{P₀:BudgetPoint}{W':ℕ→Atom su 2}
variable (H:Cash W x₀ μ L'.L Q o C T (trimP T P₀ δ β b))(U: Swathe L' d X W' P' t p' s t₁ t₂ m)
local notation "δb"=> veto (x₀:=x₀) L' d x
local notation "Xg"=> VarnC H U N
variable (r:ℂ)
local notation "C!" i=> shadeM L' d x y p q r i
open MassiveQCD.Plette
abbrev blankR (f:Side)(N:ℕ): PrintR f N Rank PEmpty PEmpty:=⟨⟨PEmpty.elim,PEmpty.elim,PEmpty.elim⟩,⟨PEmpty.elim,PEmpty.elim,PEmpty.elim⟩,fun _=> PEmpty.elim,fun _=> PEmpty.elim⟩
lemma blank_fides (V:Unit→ Site f)(Pq:BudgetPoint)(Sₐ:Support f)(κ:Lat.Frame f→ Delta Rank): (blankR f N).Fides V Sₐ Pq κ:=by
    constructor <;> intro W
    · refine ⟨fun i=>?_,fun i=>i.elim,fun i=>i.elim⟩; constructor<;> intro i <;> exact i.elim
    refine ⟨fun i=>?_,fun i=>i.elim,fun i=>i.elim⟩; constructor<;> intro i <;> exact i.elim
lemma blank_lev {W1 P A B1:ℝ}(Z:BudgetPoint)(hv:0≤a)(hh:0≤ v) (N:ℕ) (f:Side) : (blankR f N).Levy Z P W1 s t a A v:=by
    constructor <;> intro i
    · refine ⟨fun _=>0, fun i=>i.elim,?_⟩; intro i; refine ⟨fun i=>i.elim,Summable.of_finite,?_⟩; simp [hv]
    refine ⟨fun _=>0,fun i=>i.elim,?_⟩; intro i; refine ⟨fun i=>i.elim,Summable.of_finite, ?_⟩; simp [hh]
variable (xB θ α:ℝ)
local notation "κx"=> fieldD x y
local notation "Φv"=> shadeM L' d x y p q r
-- instantiate handshake.W by BlankStart or K pickup (not merged). reanchor old to embed x, new same x.
variable {I E:Type}(P0: PrintR f N Rank I E)
local notation "uV"=> taxK L x₀ 1
local notation "e!"=> ((1/32):ℝ)
local notation "tΞ"=> fan L θ x₀
local notation "Zκ"=> halo (30*radiusB x₀) {Q0}
local notation "Hκ"=> PrintR.Fides P0
variable (hKi: Wit Q o L'.L j θ x₀) -- remove
include hv hw hp hKi
lemma tin (h: P0.Fides (fun _=>Q0) {Q0} P₀ (fun W=> fieldD x y (W ∘ (sliceL L' d).embed))) (he:P0.Levy P₀ xB (fan L'.L θ x₀) e! e! (payFee Q L θ x₀) uV (MassiveQCD.Twist.spareCut 1)) (hD:2*L'.patch.radius<f.val)(hr:‖r‖≤wishGain x₀ L) : Bands L' d K H U (fun _=> Q0) δb P0 (fieldD x y) Φv ({Q0}) xB α θ:=by
    obtain ⟨h1,h2,h3⟩:= riptide L' d K Q o x y p q (N:=N) H U r θ hKi hr hD hv hw hp -- unused shadow V
    refine ⟨h,he,sum_f x y,guardOne x y,funext fun V'=>funext fun U=>h2 V' U,h3,h1⟩
omit hKi hv hw hp
local notation "Zy"=> halo P₀.B {p}
variable (S0:Support f)(Z0: Unit→Site f)(z:ℂ)
noncomputable abbrev keystone:= trestle P0 (texel L' d 0 x p) (texel L' d 0 y q) z
variable (hV:P0.Fides Z0 S0 P₀ (fieldD p q))
local notation "Zr"=>keystone L' d x y p q P0 z
include hv hw hp hV
lemma stint (V:ℝ) (h:Zy⊆ S0)(he: 2*M+ σt ≤ P₀.B) : (Zr).Fides (fun _=>Q0) ({Q0}) P₀ (fun k=>fieldD x y (k∘ (sliceL L' d).embed)):=by
     have hX: halo M {Q0}⊆ S0:= Subset.trans (fun i hi=>by obtain ⟨k,hk,hδ⟩:=halo_spec.mp hi; rw[mem_singleton.mp hk] at hδ; have hv:separation p Q0≤M:=(separation_comm ..).trans_le hv; exact halo_spec.mpr ⟨p,mem_singleton_self _,(separation_triangle p Q0 i).trans (by omega)⟩) h
     have hY: halo M {Yg}⊆ S0:=Subset.trans (fun i hi=>by
           obtain ⟨k,hk,hδ⟩:=halo_spec.mp hi; rw[mem_singleton.mp hk] at hδ; have hw: separation q Yg≤M:=(separation_comm ..).trans_le hw
           refine halo_spec.mpr ⟨p,mem_singleton_self _,(separation_triangle p q i).trans (show _ from ?_)⟩; have hq:= separation_triangle q Yg i; omega) h
     exact textT p q x y P0 (Tx) (Ty) z S0 P₀ ({Q0}) Z0 (fun _=>Q0) hV (fun k=>k∘ (sliceL L' d).embed) (fun g V=> staffT L' d 0 x p V g) (fun g V=> staffT L' d 0 y q V g) (contT ..) (contT ..) (fun X Y hv=> respects _ _ _ _ _ M le_rfl X Y (agrees_mono hv hX)) (fun X Y hv=> respects _ _ _ _ _ M le_rfl X Y (agrees_mono hv hY)) ((halo_subset ..).trans hX) (mem_singleton_self _)
omit hV hv hw hp
variable (w V Q₁ Q₂ v₁ v₂ κE:ℝ)
-- cost.R clocks at matching level B.P.From previous smaller τ. use exact standard node requirements.Lights.St.Start.
lemma levyM (hD:2*L'.patch.radius<f.val)(W:ℝ)(h:∀ X:Mat,∀ i j:Hue, ‖X i j‖≤ W*‖X‖)(hm:0≤W) (hp:P0.Levy P₀ xB w Q₁ Q₂ V v₁ v₂)(he:e!≤Q₁)(hk:e!≤Q₂) (hK:uV≤v₁) (ht: ‖z‖*(W*(Kit.scale L))^2 ≤ κE)(hι:Fintype.card Rank * (κE*V) ≤ payFee Q L θ x₀)(hz:Fintype.card Rank*(κE*v₂) ≤ MassiveQCD.Twist.spareCut 1) : (Zr).Levy P₀ xB w e! e! (payFee Q L θ x₀) uV (MassiveQCD.Twist.spareCut 1):=by
    let a:= ((T' : Teller su)); -- vv
    have hF (U:Grid f)(i j) : ‖z‖ * ‖doll (Tx U) (Ty U) i j‖ ≤ κE:=by
         unfold doll; rw[norm_mul]; apply le_trans _ ht; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); rw [pow_two]
         refine mul_le_mul ((h _ _ _).trans (mul_le_mul_of_nonneg_left (entryL L' d 0 x p U hD) hm)) ((h _ _ _).trans (mul_le_mul_of_nonneg_left ((norm_star _).le.trans (entryL L' d 0 y q U hD)) hm)) (norm_nonneg _) (mul_nonneg hm (Kit.scale_pos _).le)
    have hY:= esteem P0 (Tx) (Ty) z P₀ Q₁ κE Q₂ w v₁ V v₂ xB hp hF uV (Real.exp_pos _).le hK e! e! he hk -- order
    refine ⟨fun i=>(hY.budget i).elim fun f ⟨hp,hk⟩=>⟨f,hp,fun i=>budget_loosen (hk i) hι⟩,fun i=>?_⟩
    obtain ⟨f,hp,hq⟩:= (hY.fare i).price; exact ⟨f,hp,fun i=> budget_loosen (hq i) hz⟩
end YM.QCD.Comet
#print axioms YM.QCD.Comet.levyM
#print axioms YM.QCD.Comet.stint
#print axioms YM.QCD.Comet.tin
