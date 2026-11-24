import YM.Oars.Reseats
import YM.Oars.Come
import YM.Cardinal.Girdle
/-!
 # Spaced cube publication (higher incidence E exports through an option swizzle,
 including true overhead income). Remainders store priors on right-stamps.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {A B C I J E :Type}[Fintype A][Fintype B][Fintype C][Fintype I][Fintype J]
variable (A) (q:I→Bool)(p:J→Bool)(f:I→Option J)(g:I→J→ℝ)
local notation "R"=>Spine I
local notation "S"=>Spine J
variable (r:I→J→Prop) {P:Set (Finset J)} {D:Set (Finset I)}(hp:Pledge q p r P D) {c:Side}{N:ℕ} {a b w A₁ :ℝ}{m k i0:ℕ}(x:I→Site c)(y:J→Site c) (θ:ℝ)
include hp
local notation "M"=>Keys c 6
local notation "T"=> Patio (M⊕R)
local notation "L" j=>leaves M q p (findV r j) g
local notation "F" j=>flame M q p (findV r j) g
local notation "↑I"=>banknote 6 x θ
local notation "↑J"=>banknote 6 y θ
local notation "↓J"=> withdraw 6 y θ
local notation "↓I"=>withdraw 6 x θ
local notation "Γ" a=>loft r P a
namespace LoomT
open Massive.Poised.Plans Massive.Poised.Plans.Girdle
variable (P₀:I→Support c) (Pt:BudgetPoint) (G: Reel c 6 I E) (hG:G.Book x q)(hQ:∀ i, G.z i⊆ atlas P₀ (G.addr i).support)
-- pore alphabet.singular.decom later
local notation "N'"=> aperture -- unused
noncomputable abbrev Fellows (R₀: I→J→Prop)(P:Set (Finset J)):= Σ i:E, ↥(loft R₀ P (G.z i))
local notation "Eⁱ"=> Fellows G r P
noncomputable def swirl: Reel c 6 J (Fellows G r P):= ⟨fun i=> G.addr i.fst, fun i=> i.snd.val, fun i U=> flame M q p (findV r i.snd.val) g (G.mark i.fst U)⟩
variable (i:Fellows G r P)
local notation "G'"=> swirl (P:=P) q p g r G -- order
local notation "c0"=> Sample.purse (findV r i.snd.val) g (G.z i.fst)
omit hp in
lemma swipeL : Melts r P (G.z i.fst) i.snd.val:=(mem_filter.mp i.snd.property).2
include hG
lemma spoke : ∃ a:ℂ, ‖a‖=‖c0‖∧ Reel.speaker p G' i=a • Reel.speaker q G i.fst:=by
    let H:= (F i.2.val); obtain ⟨v,hv,hP⟩:= poke M q p (findV r i.2.val) g (hym q p r hp _ (swipeL ..).1) (G.z i.fst) (swipeL r G i).2.1; rw [(swipeL r G i).2.2] at hP; refine ⟨v*c0,by rcases hv with h|h <;> simp [h],?_⟩; funext V; let v':= G.mark i.fst V; let s:=(G.z i.fst); let P':=(hG.stage i.fst V).1; let c:= v*c0
    change scrape M (burst p i.snd.val) ((L i.snd.val) v'.val)=c • _; rw [←show stake M _ (scrape _ _ v'.val)=v'.val from P'.exact,markedOut,map_mul,hP,mul_smul_comm,leaves, AlgHom.comp_apply,tarfib,blot_left,map_smul, ← markedOut,quid]; rfl
variable (he:∀ i j,r i j→y j∈P₀ i)
include hQ he
lemma ordained : (G').Book y p:=by
    refine ⟨fun i=>?_,fun i=>?_,fun i=> ((F i.snd.val).toLinearMap.continuous_of_finiteDimensional.measurable.comp (hG.permit i.1)),fun i V W hp=> congr_arg (F i.snd.val) (hG.room i.1 V W hp),fun i V=>?_, fun i V k=>?_⟩
    · apply Finset.card_pos.mp; rw [show ((G').z i)= i.snd.val from rfl, worldM r hp.mast _ (swipeL r G i).1 _ (swipeL r G i)]; exact Finset.card_pos.mpr (hG.stays ..)
    · intro x hx; obtain ⟨j,hx1,e⟩:= Finset.mem_image.mp hx; change j∈i.snd.val at hx1; subst x; have hM:=swipeL r G i; have hk:j∈front (findV r i.2.val) (G.z i.1):= hM.2.2.symm ▸ hx1; obtain ⟨a,ha,hg⟩:= (frontM _).1 hk; exact (mem_filter.mp (hQ i.1 ha)).2 (he a j ((findG r hp.mast _ _ hM.1).1 hg).2)
    · let s:=i.snd.val; have he:Polite p s ((G').mark i V):=(countT M q p g r hp _ _ (swipeL ..) _ ((hG.stage ..).1)).1; refine ⟨he,fun j=>?_⟩; by_cases H:j=burst p s
      · subst j; obtain ⟨a,hA,hF⟩:= spoke q p g r hp x G hG i; let X:=region (limits (G.addr i.fst).support («F»:=6)); change Reel.speaker p (G') i V ∈ X; rw [hF]; exact Subalgebra.smul_mem _ ((hG.stage i.fst V).2 _) _ -- region args check
      rw [he.spectral _ H]; exact Subalgebra.zero_mem _
    · exact (drift q p g r hp _ _ _ _ k (swipeL ..) ((hG.stage ..).1)).trans (congr_arg _ (hG.tint ..))
-- revenue.O Ω. exp global R. HYP : shiftBound at μ, mixed E gains tiny.
omit hQ he
variable (Bv:ℕ)(hα:∀ i,(opts r i).card≤Bv)(hΓ:∀ i j,r i j→ |g i j|≤a)
variable (F₁:E→ℝ)(hV:∀ i,∀ j∈G.z i,Sight (G.addr i).support (x j) k Pt θ (Reel.speaker q G i) (F₁ i))
local notation "Ξ"=> Girdle.tariff i0 k Pt.power Pt.order
variable (hΨ:∀ i j,r i j→ separation (x i) (y j) ≤ i0)(ht:0<θ)
include hV hΨ ht
lemma reads (j:J)(hj:j∈i.snd.val): Sight ((G').addr i).support (y j) k Pt θ (Reel.speaker p G' i) ((Ξ*F₁ i.fst)*‖c0‖):=by
      have hY:=swipeL r G i; obtain ⟨q,hq,hA⟩:= (frontM _).1 (hY.2.2.symm ▸ hj); obtain ⟨c',hc,hS⟩:= spoke _ _ g r hp x G hG i
      have hΦ:= moving (hΨ q j ((findG r hp.mast _ _ hY.1).1 hA).2) _ (hV _ _ hq) ht; rw [hS,mul_comm _ ‖_‖,← hc]; exact Massive.Poised.Counting.Terrain.scaledL hΦ _ -- inspect
end LoomT
end YM.MassiveQCD.Sample
