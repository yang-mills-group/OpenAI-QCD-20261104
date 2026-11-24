import YM.MassiveQCD.Venture.Fair
import YM.MassiveQCD.Relight.Pledge
import YM.QCD.Finch.Degree
/-! # PortC converted receipts at analytic tilt. Use at same supports of Claim.* after structural transport. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Finch
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Cove Leaf Lat Creek Loom
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden Footprint Bay Run Jets.Sun Pine Grass Sway OrbitG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f:Side}{P:Teller su}{δ β b τ μ W C:ℝ}{Q:Target su P}{o :Target.Order su W}{R:BudgetPoint}{N m l n i j k:ℕ}
variable {Y:StepData c f} {η p h z a a' t v u u' q:ℝ} {D E J:Type}[Countable E][Countable J][Fintype D]
open AnalyticBridge.GaussianFieldAlignment Locations Channels PhysicalNext.Repeat.Turn Next.Fluctuations Next.SectorChange
local notation "B" => radiusB τ
open Sway OrbitG Strut Revolve
variable {W' :ℕ→Atom su 2}{J':Plan k}
variable (O:Flight j k)(K: KernelChoices)(d:f.val=c.val*O.L.val)
set_option quotPrecheck false
local notation "S"=> (O.visit K d).ratio
variable {T : Tube su (O.visit K d)}
variable {X:Grid f→Sheet f} (H:Cash W τ μ O.L Q o C T (trimP T R δ β b))(G:Sun O c f d η h z a a' m X) (U :Swathe O d X W' J' h η a u v i)
variable {Γ: Land c (Site c) (Site c)}{D':Pays c (Site c) (Site c)}
variable (Y': Rise f N E J)
local notation "Z'"=> tableau O d K Y' H G U Γ
open PhysicalNext.Repeat.Greenbelt Territory GasP Ursell Graph
open scoped PhysicalNext.Repeat.Greenbelt
-- Receipt all real; with Penalty tickets launch in code, no downstream jets/projectors!
open Patron
variable (χ: Chi)
variable {κ κ':Type}
open Stew Reggae Entr Kites Calm Grove Stem Villa
variable {p':BudgetPoint}{τ' B' A A' C' V' r z'  α σ g v' Θ ξ ε :ℝ}
-- avoid implicit TC indexing `Cluster (S x)` with Metric radii across equal layouts: represent in a common Fleet then charge this single prop.
structure EarnedC {c f L:Side}{N:ℕ}{St₁:StepData c f}{T:Tube su St₁}{Q: Target su P}
    {M: Rep su f}{H':Cash W τ μ L Q o C T M}{ι:Type}(F:Fleet H' ι N)(χ:Chi)(p:BudgetPoint)(σ v:ℝ):Prop where
    dark: Countable F.Dark
    bright : Countable F.Bright
    faber: Countable F.Faber
    reg: Rail.Reg (claim F χ) p.threshold
    wins : Quits (claim F χ) p.B 1 (priceK L μ τ) σ v
    glow: F.Famous
    offers (U:Grid c): Summable (F.honest χ U)
    tickets : Colorful F → MixedInk (claim F χ)
lemma darkC (hp:PortC O K d H G U Y' Γ Θ v' σ)(hz:p'.B=radiusB τ)(hW:p'.threshold=Pressure.temp τ): EarnedC (Z') χ p' σ v':=by
    let Z:= tableau O d K Y' H G U Γ; let X₀:= Wound (roof (G.equip N B) Y' 30 B) ⊕ Varn f c⊕ Gaze c; have hv :0 < radiusB τ:= hz ▸ p'.B_pos
    haveI : Countable (Pipe.Clump (O.visit K d) X₀):= counting O K d X₀
    haveI : Countable Z.Dark:=by unfold Dark; infer_instance
    haveI : Countable Z.Bright:=by unfold Bright; infer_instance
    haveI : Countable Z.Faber:=by unfold Faber; infer_instance
    obtain ⟨ht,hQ,he⟩:=PortC.meta O K d H G U Y' hp hv
    have hh V:= ((hp.scores χ).1 V).1; refine ⟨inferInstanceAs (Countable Z.Dark),inferInstanceAs (Countable Z.Bright),inferInstanceAs (Countable Z.Faber),hW.symm ▸ plumK _ _ ht hQ he hp.wordsP,?_ ,ht, hh, fun hc=> dusk_color _ _ ht hc hh⟩
    rw [hz]; obtain ⟨f,hf,hx⟩:=(hp.scores χ).2.2.2.2; exact ⟨f,hx,fun i U=>hf U i⟩

-- Spin at one shared rig.E. Stages path orientations real. Get σ receipts
section fleet
variable {L:Side}{St₁:StepData c f}{T₁:Tube su St₁}{M: Rep su f}{H':Cash W τ μ L Q o C T₁ M}{ι:Type}(F:Fleet H' ι N) (r₁:ℂ→ι→Grid f→Grid c→EvenA c N)
open Ruby Ruby.LanternK
noncomputable def lampsC (χ:Chi): LanternK c N (F.Faber):= ⟨(claim F χ).addr,fun z=> (claim (tintF F (r₁ z)) χ).warp⟩
lemma agreementK (z:ℂ): (lampsC F r₁ χ).get z=claim (tintF F (r₁ z)) χ:=rfl
lemma craftK (χ:Chi)(d:ι→ℕ)(h:∀ z:ℂ,‖z‖≤1 → EarnedC (tintF F (r₁ z)) χ p' σ v')(hv:∀ z:ℂ,‖z‖≤1→∀ i U V,r₁ z i U V=z^(d i) • F.works i U V) : (lampsC F r₁ χ).ChargedK 1 p'.threshold v' 0 p'.B σ (priceK L μ τ) :=by
    have he z (hz:z∈Metric.ball 0 (1:ℝ)):= h z ((mem_ball_zero_iff.mp hz).le); refine ⟨Real.exp_pos _,fun z hz=> (he z hz).reg,fun z hz=> (he z hz).wins,?_⟩; intro j x; apply fundsRead _ d r₁ x χ hv ?_ (fun z hz=> (h z hz.le).glow); have hz:tintF F (r₁ 1)= F:= by
       unfold tintF; rw [show r₁ 1=F.works from funext fun i=>funext fun U=>funext fun V=>by simpa only [one_pow,one_smul] using hv 1 (by simp) i U V]
    -- avoid Summable congr cast
    exact hz ▸ ((h 1 (by simp)).offers x)
end fleet
end YM.QCD.Finch
#print axioms YM.QCD.Finch.craftK
