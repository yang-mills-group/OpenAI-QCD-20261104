import YM.QCD.Loom.Many
import YM.QCD.Loom.Kiss
/-! # Full bill at pre-reset. Meristem & habitat further -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Creek
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden Footprint Bay Run Jets.Sun Pine Grass
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f s:Side}{P:Teller su}{δ β b τ μ W C d':ℝ}{Q:Target su P}{o :Target.Order su W}{R:BudgetPoint}{N m l n i j k w₂:ℕ}
variable {η p h z a a' t v V u u' q θ w₁:ℝ} {E K:Type}[Countable E][Countable K]
variable (L:Flight j k)(d:f.val=c.val*L.L.val)(O:KernelChoices)
variable {T : Tube su (Flight.visit L O d)} {W' :ℕ→Atom su 2} {P':Plan k}
variable {X : St f}
local notation "S"=> Flight.visit L O d
local notation "PI"=> trimP T R δ β b
variable (E₁:Rise f N E K)(H:Cash W τ μ L.L Q o C T (trimP T R δ β b)) (G:Sun L c f d η h z a a' m X) (V':Swathe L d X W' P' h η a u v i)
local notation "R'"=> radiusB τ
local notation "Z"=> G.equip N (radiusB τ)
local notation "U"=> roof (Z) E₁ 30 R'
variable (Γ: Land c (Site c) (Site c)){Y: Pays c (Site c) (Site c)} (F:Tree.Forest (S).ratio)
set_option quotPrecheck false
local notation "P₀"=> (tableau L d O E₁ H G V' Γ).suitcase F
local notation "uV"=> fan L.L (1/4) τ
local notation "π"=> demandQ L.L θ τ
local notation "φ"=>18*R'
local notation "a₂"=> shiftCost L.L τ (romp L.L)
local notation "UC"=> unitsP Q L.L μ β τ C a₂ π
local notation "Y'"=> deckHue H (Z) E₁ (U)
local notation "Σx"=> sailP H Γ N -- wrong H Rep? correct
local notation "Σy"=> VarnC H V' N
variable {s1: Varn f c→ℝ}{s2:Gaze c→ℝ}
def River (F0:Tree.Forest (Flight.visit L O d).ratio) (θ a'':ℝ) (Γ0:Land c (Site c) (Site c))(Y:Pays c (Site c) (Site c))(u' d' v':ℝ)(w0:ℕ):Prop :=
   let X1:=tableau L d O E₁ H G V' Γ0
   let f:= X1.suitcase F0
   X1.Famous ∧ (∃ w, f.Depth (unitsP Q L.L μ β τ C (shiftCost L.L τ (romp L.L)) (demandQ L.L θ τ)) w (fun _=>0) ∧ Summable w ∧ 1≤a'' ∧ (∀ V,f.solves V) ∧ (∀ X,Placid E₁ R.threshold X) ∧ f.Merit w (shiftCost L.L τ (romp L.L)) (token c N a'')) ∧ Run.Pack id id u' d' w0 (wood P' 0 L.land) v' Γ0 Y

lemma knit (F: Tree.Forest (Flight.visit L O d).ratio) {s0: Wound (U) → ℝ}(d0: Run.Pack id id w₁ d' w₂ (wood P' 0 L.land) q Γ Y)
(hP:(tableau L d O E₁ H G V' Γ).Famous) (ht:Fleet.Theft Y' F (fun _=>0) s0 t uV ∅ 0 0)
(hT:Fleet.Theft Σy F (fun i=>siteH i (S).ratio) s1 t uV (univ.filter fun i=> waxV i=none) φ ((S).ratio.count.val^4+1))
(hz:Fleet.Theft Σx F Prod.fst s2 t uV (univ.filter fun i=> i.2=none) φ 1)
(p0: Ac.Hit (Y').ground R' s0 Q.relative (bootstrut L.L θ τ))(p1:Ac.Hit (Σy).ground R' s1 Q.relative (betaF su τ L.L ^ (-(3/8):ℝ)))(p2:Ac.Hit (Σx).ground R' s2 Q.relative (betaF su τ L.L ^ (-(3/8):ℝ)))
(hD: (UC).Buy L.L Q.halo R')(hp:Summable s0∧∀ V:Grid c,((Y').suitcase F).solves V)(hw:∀ X,Placid E₁ R.threshold X)(hv:1≤t): River L d O E₁ H G V' F θ t Γ Y w₁ d' q w₂:=by
   refine ⟨hP,?_,d0⟩
   let Y₀ := deckHue H (Z) E₁ (U); let Y₁:= VarnC H V' N; let Y₂:= sailP H Γ N
   have hx:= balanceP (united Y₁ Y₂) ht (balanceP Y₂ hT hz); let pT:=(tableau L d O E₁ H G V' Γ).suitcase F; let sX:= Sum.elim s0 (Sum.elim s1 s2); change ∃ f,pT.Depth _ f _∧ _ -- may p wrong order
   let A:= unitsP Q L.L μ β τ C a₂ π
   have hA : Ac.Hit pT.ground R' (tariff sX (fun _=>0) (fun _=>0) Q.ε) Q.relative π:=by
      have he: (tariff sX (fun _=>0) (fun _=>0) Q.ε)=sX:=by ext; simp [tariff]
      rw [he]; exact Labels.together _ _ _ p0 (Labels.together _ _ _ p1 p2)
   refine ⟨sX,Pipe.surveyP pT rfl hx.grow (fun _=>le_rfl) _ _ hD hA, Summable.sum _ hp.1 (hasSum_fintype _).summable,hv,(fun V=>legible H Y₀ (united Y₁ Y₂) V (hp.2 V) hP),hw,?_⟩
   have hv:= watch _ hx; rw [show max 0 (max (18*radiusB τ) (18*radiusB τ))= 18*radiusB τ by omega,show 0+(_+1)=romp L.L from ?_] at hv; rotate_left
   · rw [zero_add]; rfl
   exact hv
end YM.QCD.Loom
