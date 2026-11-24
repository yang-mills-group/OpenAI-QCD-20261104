import YM.MassiveQCD.Plate.Wrap
import YM.MassiveQCD.Pavilion.Sill
/-! # Shape, occupancy and money for ALL marked steps over one fixed real tilt.
 Keep the full Reagan (incl bonds+support+history before geometry call). `Station` fires with large rate permit capacities in Powers (all BEFORE and unmarked docs to come). -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove Cupola Kites Shells Warmlet
open PhysicalNext.Repeat.Greenbelt
open scoped PhysicalNext.Repeat.Greenbelt Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}{R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}{H:Cash W τ μ L Q o C T R}{ι κ I E J D Q₀:Type}{N:ℕ}
variable {j k m i k₁ n:ℕ}{z η p h a a' hQ v δ b s u q:ℝ}{P' : Plan k}{X:Run.St f}
variable (Lp:Side)
local notation "b'"=> radiusB τ
abbrev kt0:ℝ := (6/32) -- MARK quiescent on output. Next readiness adjustment must spend.
abbrev ξK:ℝ:= (1/64)
abbrev coatPriceK (L:Side)(x μ:ℝ) := priceK L (μ/2) x
abbrev τpriceK (L:Side)(x μ:ℝ) := priceK L (μ/2/2) x
abbrev allowPriceK (L:Side)(x μ:ℝ):= (priceK L ((μ/2)/4) x)⁻¹
abbrev waxT (L:Side)(x:ℝ):ℝ:= 4*pra L x
variable (t:ℝ)
structure Appointment (L:Side)(μ x:ℝ)(t:ℕ)(τ φ:ℝ) :Prop where
    paysT: 1 ≤ priceK L μ x ∧ 1≤ coatPriceK L x μ
    guard : 8 ≤ radiusB x
    general : |φ|≤ Real.exp (τ/128*radiusB x)
    loom : ∀ (ι κ:Type)(c: Side)(N:ℕ)(Y:Ruby.Hue c N ι)(X:Patron.Rail c N κ)(p:BudgetPoint)(t:ℝ), p.B=radiusB x → Quits X p.B 1 (priceK L μ x) (1/4) t → Relight.Wax Y p.threshold p.B (1/4+1) (waxT L x) t → Quits (Ruby.Trail Y X p.threshold) p.B 1 (coatPriceK L x μ) kt0 t
    Hearth (σ:ℝ)(N:ℕ)(c:Side)(U I:Type)[Fintype I](F: Patron.Rail c (ample N I) U)(A:Set (Finset I))(p:I→ Site c)(q:I→Bool)(b:ℝ)(w:I→ℝ): Fires p t → (∀ i∈A,Spaced p i (radiusB x)) → Pill F b σ (radiusB x) kt0 (coatPriceK L x μ) → (∀ i U,Well N p σ q (F.warp i U)) → (∀ i, |w i|≤ |φ|) → 0<σ → Film.Stock N (Film.publication N p q F A σ) (radiusB x) (τpriceK L x μ) (5/32) σ (allowPriceK L x μ) w
lemma allotQ {w:ℝ→ℝ}(v:ℝ)(k:ℕ)(hv:0<μ)(h:Rate su L v w)(he:0<a): ∀ᶠ x:ℝ in atTop, Appointment L μ x k a (w x):=by
    filter_upwards [Reel.playability L v w he h, Work.E01.radiusB_tendsto.eventually_ge_atTop 8, Ruby.bearW L μ kt0 (1/16) 4 1 hv (by norm_num [kt0]) (by norm_num) (by norm_num) zero_lt_one, Film.govern ξK L (μ/2) k (by norm_num [ξK]) (5/32) (by linarith) v h] with x hX hz ht hP
    refine ⟨⟨Real.one_le_exp ?_,Real.one_le_exp ?_⟩,hz,hX,?_,?_⟩
    · unfold Delay.hatWin; positivity
    · unfold Delay.hatWin; positivity
    · intro I J c N Y P Xv t hb hu hY; refine ht c N I J Y P Xv t hb ?_ ?_
      · rwa [show kt0+1/16=(1/4:ℝ) from by norm_num [kt0]]
      rwa [show kt0+1/16=(1/4:ℝ) from by norm_num [kt0]]
    intro σ N c T I _ U A p q b w hu hz hs; apply hP; assumption; assumption; rwa [show ((5:ℝ)/32)+2*ξK=kt0 from by norm_num [kt0,ξK]] -- syntax forall implication?
-- `castPill` from Asset and ANY Field.Scheduled.
namespace SC
lemma time_trip (P:BudgetPoint)(K₀: Fleet H ι N)(χ:Chi)(hp:K₀.Famous)(hf:Territory.Gate K₀)(hk:K₀.Feasible)(hx:Colored K₀)(he:K₀.speaking)[Countable K₀.Bright][Countable K₀.Faber](h:∀ x:Grid c,Summable (K₀.honest χ x))(a t L :ℝ)(hb:P.B=radiusB τ)(hP:P.threshold=Pressure.temp τ)(hθ:1/4≤a)(hy:0<t)(_hp:1 ≤ L)(Hoh:∃ g: K₀.Faber→ℝ,(∀ V:Grid c,∀ x: K₀.Faber,‖token c N t (K₀.mission χ V x.val)‖ ≤ g x)∧ Ac.Hit (fun x:K₀.Faber=>GasP.wound K₀.broad x.val) (radiusB τ) (taxed (fun i:K₀.Faber=> GasP.sweep K₀.invD i.val) g L) a 1): Pill (claim K₀ χ) P.threshold t P.B (1/4) L:=by
    obtain ⟨f,h1,h2⟩:= Hoh; let Y:= claim K₀ χ; have hv: Quits Y P.B 1 L a t:=by rw [hb]; exact ⟨f,h2,fun i V=>h1 V i⟩
    refine ⟨hP.symm ▸ plumK K₀ χ hp hf hk he,?_, Finch.liveK Y hv hθ hy le_rfl⟩; -- indentation semicolon after hv. maybe hv eats.
    intro i Xg k; exact congr_arg Subtype.val (marchW K₀ (hx.warp k) hp χ Xg (h _) i.val)
variable (L':Flight j k)(d:f.val=c.val*L'.L.val)(K:KernelChoices)
local notation "S'"=> Flight.visit L' K d
variable {T:Tube su (Flight.visit L' K d)}{W':ℕ→Atom su 2}
variable (H:Cash W τ μ L'.L Q o C T (trimP T O δ β b)){P₀:Rise f N E J} [Countable E][Countable J]
variable (G:Sun L' c f d η h z a a' m X) (U :Swathe L' d X W' P' h η a u v i) (Γ:Land c (Site c) (Site c)){D':Pays c (Site c) (Site c)}
variable [Fintype I] (Y:Stitch.Tablet P₀ I)(A:I→Site f)(φ:ℝ)
local notation "M"=> Ribbon.ample N I
local notation "R'"=> trimP T O δ β b
local notation "B"=> radiusB τ
local notation "Zⁱ"=> QCD.Jets.Touch.roof (G.equip N (radiusB τ)) P₀ 30 B -- namespace? roof unqualified
local notation "Tx"=> vantage L' d K H G U Γ Y A φ
local notation "Vx"=> tableau L' d K P₀ H G U Γ
set_option quotPrecheck false
local notation "loc"=> ((S').ratio.parent ∘ A)
local notation "Β" => Ribbon.banknote N loc φ
local notation "I'"=> Ribbon.Spine I
local notation "mx"=> Keys c N ⊕ Ribbon.Spine I
local notation "d!"=> (vacR I' (Keys c N)).comp (withdraw N loc φ)
variable (q':I→Bool)
local notation "R₁"=> Sum.elim (fun (u:Wound (Zⁱ)) => Y.markers u.val) (fun _:Varn f c ⊕ Gaze c=>∅)
variable {χ:Chi}{θ θ₁:ℝ}{Pq:BudgetPoint}
variable (hx:Neat Y)(he:Supplies L' d K H G U Γ Y A φ χ q' θ θ₁ Pq.order Pq.power)
local notation "Yq"=> claim Tx χ
local notation "w'"=> priceK L'.L μ τ
include he
lemma summableQ (x:Grid c) : Summable ((Tx).honest χ x):=by obtain ⟨F⟩:= Tree.select (S').ratio L'.odd; exact (Supplies.reveals L' d K H G U Γ Y A φ he F x).1
lemma Pillar (hb:Pq.B=radiusB τ)(hP:Pq.threshold=Pressure.temp τ)(hθ:1/4≤θ)(hp:1 ≤ priceK L'.L μ τ): Pill Yq Pq.threshold φ Pq.B (1/4) (priceK L'.L μ τ):=by
    let v:= he.title; have ht:=v.favorable; let C:=Tx; let PS:= Yq; let X₀:= Wound Zⁱ ⊕ Varn f c⊕ Gaze c
    haveI : Countable (Pipe.Clump (L'.visit K d) X₀):= QCD.Villa.counting L' K d X₀ -- order
    haveI : Countable (Tx).Bright:=by unfold Bright; infer_instance
    haveI : Countable (Tx).Dark:=by unfold Dark; infer_instance
    haveI : Countable (Tx).Faber:=by unfold Faber; infer_instance
    exact time_trip Pq (Tx) χ ht ⟨v.gator⟩ v.sturdy v.color v.voice (summableQ L' d K H G U Γ Y A φ q' he) θ φ _ hb hP hθ (zero_lt_one.trans_le he.strength) hp (Supplies.forced L' d K H G U Γ Y A φ he)
end SC
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.SC.Pillar
