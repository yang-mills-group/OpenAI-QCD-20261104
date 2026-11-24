import YM.QCD.Purse.Table
import YM.QCD.Tax.Glory
import YM.QCD.Purse.Board
import YM.MassiveQCD.Column.Throne
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
variable (V:Cash W s μ L Q o C T (lore (trimP T R δ β B₀)))
variable {p:ℝ}{t₀:Fj D E J→ℝ}
local notation "o!"=> trunkP H Y P' Y' V
lemma getsWage (hv: Ready (roof P' Y' Q.halo ζ) ζ t₀ a u 1 r)(he:2*r<1)(hx:0 < p)(hz:0≤q)(ha:0≤a): Ac.Hit (fun i:A⁔=> ((o!) i).support) ζ (wageP H Y P' Y' V p q t₀) a ((q*p⁻¹)*(2*u*(2*r)^1*(1-2*r)⁻¹)):=by
    intro x; let R i:= roof P' Y' Q.halo ζ i; let d:A⁔ → Finset (Fj D E J):= fun i=> i.label.val; let A (i: Finset (Fj D E J)):= i.biUnion R
    have hI : Function.Injective d:=iden H Y P' Y'; have hh:=budget_pull d hI (bold hv he ha hx hz (sky P' Y') A x (fun _=>Subset.refl _)); refine budget_mono hh ?_ ?_
    · intro i
      apply ite_nonneg _ le_rfl
      apply mul_nonneg _ (Real.exp_pos _).le
      unfold wageP; apply ite_nonneg _ le_rfl
      have hm:0 ≤ ∏ j∈ i.label.val,t₀ j :=prod_nonneg (fun i _=>hv.2.2.2.2.1 i); positivity
    intro i; by_cases he':Small H Y P' Y' i V∧2≤ i.label.val.card; swap
    · rw [wageP,if_neg he']; simp only [zero_mul,ite_self]; exact hh.1 _
    have ht : ((o!) i).support = A (d i):= by rw [trunkP,if_pos he'.1]; exact (plateK H Y P' Y' V i).1
    split
    next hz=>
       have he : x ∈ A (d i):=ht ▸ hz -- substitution?
       rw [wageP,if_pos he',if_pos (And.intro he'.2 (And.intro he i.label.property))]; dsimp only; rw [ht]; exact le_rfl
    next h=> exact hh.1 _
end Warmlet
lemma versionBooths (L:Side)(V:Libretto su j)(Z:Hera.Rights su j)(p:ℕ)(θ:ℝ)(he:0<θ):∀ᶠ x in atTop,2*fan L (-θ) x<1∧ ∀ I:BudgetPoint,I.power=p→(caseT V Z I L x*(cashM L θ x)⁻¹)*(2*fan L (-θ-θ/2) x*(2*fan L (-θ) x)^1*(1-2*fan L (-θ) x)⁻¹) ≤ fan L (-θ/4) x*chip L x:=by
   obtain ⟨g,hg,h⟩:= courage L V Z p
   let G x:=fan L (-θ-θ/2) x; let d x:=2*fan L (-θ) x; let z x:=fan L θ x; let k x:=g x*z x ^2
   have ht: Seat L (-θ) d:= Seat.keeps.timesL 2; have hf:Seat L (-θ-θ/2) G:=Seat.keeps
   have hv: Seat L (0+θ*(2:ℕ)) k:= hg.ponies (Seat.keeps.powered 2)
   have he':Seat L (-θ/2) (fun x=>k x*(2*G x*d x*2)):= ((hv.ponies (((hf.timesL 2).ponies ht).times 2)).above (by push_cast; linarith))
   filter_upwards [he' (-θ/4) (by linarith),ht.shrinks (by linarith) (D:=1/2) (by norm_num),Delay.shift_pos su L] with x hx hX hA
   have hz:=le_trans (le_abs_self _) hX; refine ⟨hz.trans_lt (by norm_num),fun I he=>?_⟩
   let c:=Jets.Touch.chip L x; have hV:0<c:=healthy_chip hA; have hZ:0 ≤ g x:=by rw [h _ _ he]; linarith only [caseN V Z I L x]
   have ht':0< z x:=fan_pos ..; rw [←h _ _ he,pow_one,show (cashM L θ x)⁻¹=z x^2*c from ?_]
   · rw [show _ * (_ * _ *(1- _ )⁻¹) = (k x*(2*G x*d x*(1-d x)⁻¹))*c from by unfold k G d; ring]
     apply mul_le_mul_of_nonneg_right _ hV.le; apply le_trans _ ((le_abs_self _).trans hx); have hQ : (1-d x)⁻¹ ≤2:= by rw [inv_le_iff_one_le_mul₀ (show 0<1-d x by linarith)]; linarith
     have he₀:0 ≤ 2*G x*d x:=by unfold G d; positivity [fan_pos L (-θ-θ/2) x,fan_pos L (-θ) x]
     exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ he₀) (by unfold k; positivity)
   unfold cashM Jets.Touch.rust z c; simp [mul_comm]
noncomputable def tiltPot (L:Side):=1+Real.log L.val
lemma tiltPot_pos (L:Side):0<tiltPot L:=by
   have hr : 1 ≤ (L.val:ℝ):=by exact_mod_cast (show 1 ≤ L.val from L.pos)
   unfold tiltPot; linarith only [Real.log_nonneg hr]
lemma log_throne (u a ψ:ℝ)(p ℓ:ℕ)(N':Libretto su j)(K:Hera.Rights su j)(hu:0<u)(ha:0≤a):∃ n:ℕ,∀ L:Side,n≤L.val→Capstone L ℓ p u a (fern L * tiltPot L) N' K ψ:=by
    obtain ⟨C,m,hC,hp⟩:= stable_throne u a ψ p ℓ N' K hu ha
    obtain ⟨n,hn⟩:= Filter.eventually_atTop.1 ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop C)
    refine ⟨m+n,fun L hl=>?_⟩; constructor; intro O hv c f F hf k b m' hl' hx; have hg : C ≤ tiltPot L:=(hn L.val (by omega)).trans (le_add_of_nonneg_left zero_le_one); exact ((hp L (by omega)).lots O hv c f F hf k b m' hl' hx).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (fern_pos _).le) (Real.exp_pos _).le)
-- boost exponent after restoring fern scale.
namespace Warmlet
variable {σ ε ψ:ℝ} (V:Cash W s μ L Q o C T (lore (trimP T R δ β B₀))) (Λ:Hera.Rights su j)
set_option maxHeartbeats 350000 in
lemma honor (hd:Capstone L (Q.halo+8) O.power A B (fern L*ε) N' Λ ψ) (he:P'.trim≤ζ)(hp:P'.trim+1≤ R.B+R.B)(hv:R.B≤ 2*ζ)(hz:0<ζ)(h':0 ≤ σ)(p:Duke H Y P' Y'):
      fern L ^5*σ *fluteT N' Λ O ψ (coverNumber R.B (brimW P' Y' p.val.label.val)) ≤ fern L^5*(ε*σ)*Real.exp (A*coverNumber R.B (Y'.row (col H Y P' Y' p)).support-B*coverNumber ζ (perch H Y P' Y' V p.val).support):=by
       let i:= col H Y P' Y' p; let k:= coverNumber ζ (perch H Y P' Y' V p.val).support; let v':=coverNumber R.B (Y'.row i).support; let T':=fluteT N' Λ O ψ (coverNumber R.B (brimW P' Y' p.val.label.val)); let fΩ:=fern L; let χ:=Real.exp (B*k); let p':=(L.val:ℝ); have hp':0<p':=by unfold p'; positivity
       have hm:fΩ^5*p'^4=fΩ:=by unfold fΩ fern p'; field_simp
       have hh := hd.lots O rfl c f S.ratio H.laws.data.funds.length_eq k _ _ (sizeP H Y P' Y' p hp) (terrestrial H Y P' Y' V p he hv hz); change fΩ^5*T'*χ*p'^4≤ fΩ*_*Real.exp _ at hh
       rw [Real.exp_sub,←mul_div_assoc]; apply (le_div_iff₀ (Real.exp_pos _)).mpr; apply le_of_mul_le_mul_right _ (pow_pos hp' 4); change fΩ^5*σ *T'*χ*p'^4≤_; rw [show fΩ^5*σ*T'*χ*p'^4=σ*(fΩ^5*T'*χ*p'^4) from by ring]; apply (mul_le_mul_of_nonneg_left hh h').trans_eq; change σ*(fΩ*ε*Real.exp _) = fΩ^5*_ * Real.exp _ * p'^4; -- expose eq.
       calc _ = (fΩ^5*p'^4)*(ε*σ)* Real.exp (A*coverNumber R.B (Y'.row (col H Y P' Y' p)).support) := by rw [hm]; ring
            _ = _:=by ring
end Warmlet
end YM.QCD.Shells
