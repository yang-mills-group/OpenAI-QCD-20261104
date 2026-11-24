import YM.Oars.Planetaria
import YM.Oars.Plucks
import YM.Cardinal.Quad
/-!
 # Interpolating alpha addresses and punches, votes. F pulses at lift selector. Cost on each request (over predecessor).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {A B C I J E:Type}[Fintype A][Fintype B][Fintype I][Fintype J]
variable (A) (q:I→Bool)(p:J→Bool)(f:I→Option J)(g:I→J→ℝ)
local notation "R"=>Spine I
local notation "S"=>Spine J
local notation "Z"=> A⊕R
variable (r:I→J→Prop) {P:Set (Finset J)} {D:Set (Finset I)}(hp:Pledge q p r P D){c:Side} {a b w A₁ :ℝ}{m k i0 N:ℕ}(x:I→Site c)(y:J→Site c) (θ:ℝ)
local notation "M"=>Keys c 6
local notation "T'"=> Patio (M⊕Spine J)
local notation "T"=> Patio (M⊕R)
local notation "L" j=>leaves M q p (findV r j) g
local notation "F" j=>flame M q p (findV r j) g
local notation "↑I"=>banknote 6 x θ
local notation "↑J"=>banknote 6 y θ
local notation "↓J"=>withdraw 6 y θ
local notation "↓I"=>withdraw 6 x θ
local notation "Γ" a=>loft r P a
namespace LoomT
open Card Card.Iris Stags
variable (P₀:I→Support c)(Pt:BudgetPoint)(G: Reel c 6 I E) (hG:G.Book x q)(hQ:∀ i,G.z i⊆ atlas P₀ (G.addr i).support)
local notation "Eⁱ"=>Fellows G r P
local notation "G'"=>swirl (P:=P) q p g r G
-- eq transports
noncomputable abbrev Single (i:I):={k:E// G.z k={i}}
abbrev To (j:J) := {i:I//r i j}
noncomputable def entrant (j:J):Finset I:=Finset.univ.filter fun i=>r i j
instance (j:J) : Fintype (To r j):= Fintype.subtype _ (fun i=> mem_filter (s:=Finset.univ) |>.trans (and_iff_right (mem_univ _)))
include hp
variable (i:I)(j:J)(h₀:∀ j:J,{j}∈P)
include h₀
noncomputable def translateK (j:J)(h0:∀ j:J,{j}∈P) : (Σ i: To r j, Single G i.val) ≃ Single G' j :=by
    have hE (p:To r j)(k:Single G p.val) : Melts r P (G.z k.val) {j}:= k.property.symm ▸ Sample.meeting r hp.mast p.val _ (h0 _) p.property
    let g0 (k:(Σ i: To r j, Single G i.val)): Eⁱ:= ⟨k.2.val,⟨{j},mem_filter.mpr ⟨mem_univ _,hE k.1 k.2⟩⟩⟩
    let f(x): Single G' j:= ⟨g0 x,rfl⟩; refine Equiv.ofBijective f ⟨fun z m h=>?_,fun z=>?_⟩
    · let t:= g0; have hv: z.2.val=m.2.val:=congr_arg Sigma.fst (show g0 z=g0 m from Subtype.ext_iff.mp h); have hy:z.1=m.1:=Subtype.ext (Finset.singleton_injective (z.2.property.symm.trans ((congr_arg _ hv).trans m.2.property))); rcases z,m with ⟨⟨z,b⟩,y,c⟩; change z=y at hy; subst y; exact Sigma.ext rfl (heq_of_eq (Subtype.ext hv))
    have h: z.val.snd.val= {j}:=z.property; have hx :=swipeL r G z.val; have hN:(G.z z.val.fst).card=1:=((worldM r hp.mast _ hx.1 _ hx).symm.trans (by rw [h,Finset.card_singleton])); obtain ⟨i,H⟩:=card_eq_one.mp hN; let s:To r j:= ⟨i,Sample.solo r hp.mast i j (Eq.mp (congr_arg₂ (Melts r P) H h) hx)⟩; let k: Sigma fun i:To r j=> Single G i.val:= ⟨s,⟨z.val.fst,H⟩⟩; exact ⟨k,Subtype.ext (Sigma.ext rfl (heq_of_eq (Subtype.ext h.symm)))⟩
local notation "J₀"=>translateK q p g r hp G j h₀ -- parameter order
-- eh.
lemma renderer (v:To r j)(k:Single G v.val): (G').mark (J₀ ⟨v,k⟩).val=fun V=> (F ({j}:Finset J)) (G.mark k.val V):=rfl
lemma locPrint (v:To r j)(k:Single G v.val): (G').addr (J₀ ⟨v,k⟩).val = G.addr k.val:=rfl
include hG
lemma postage (v:To r j)(k:Single G v.val): Reel.speaker p G' (J₀ ⟨v,k⟩).val=(↑(g v.val j):ℂ) • Reel.speaker q G k.val :=by
    funext V; let Y:=G.mark k.val V; let j':=J₀ ⟨v,k⟩; unfold Reel.speaker; rw [j'.property,k.property,renderer]; let Q:=F ({j}:Finset J); have hE:= edgeS M q p g r hp v.val j {j} (h₀ _) (mem_singleton_self _) v.property Y (k.property ▸ (hG.stage k.val V).1);
    refine Eq.trans (congr_arg (scrape M (burst p {j})) hE) ?_; rw [map_smul,quid]; rfl
-- ext expenses.
end LoomT
end YM.MassiveQCD.Sample
