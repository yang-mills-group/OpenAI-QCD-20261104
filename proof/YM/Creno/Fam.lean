import YM.Bwana.Onyx
import YM.Creno.Tint
/- two-option spectra.Crease assembly alphabet protocol. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew Function
open Lattice Wilson Creek Lat Kit NormedSpace RG Cove Filter Run
open Loom Fleet MeasureTheory Ribbon Cupola Plate Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
namespace Eole.Triple
variable {I:Type} [Fintype I](q:I→Bool)
-- tags: false=pair/true=prediction mark. C flag same as first, second always even.T shape.Sig.
local notation "J"=> I × Fin 3
local notation "V"=> I × Bool
def pairLip :I ×Bool→Bool:=fun x=> if x.2 then false else q x.1
def triple :I ×Fin 3→Bool:=fun x=> if x.2=1 then false else q x.1
-- Ensure output flag.Combin.Q.variants
noncomputable def pack₂(I:Type)[Fintype I]:Bloc (I × Bool) I:= {
     unit_:= Prod.fst, arm:= fun i=>[(i,false),(i,true)],active:=fun i=>by simp,scoop:=fun i=>by simp,complete:=by rintro ⟨i,a|a⟩ j <;> simp }
noncomputable def pack₃ (I:Type)[Fintype I]:Bloc (I ×Fin 3) (I ×Bool):= {
     unit_:= fun x=> (x.1,decide (x.2=2)), arm:= fun i=> if i.2 then [(i.1,2)] else [(i.1,0),(i.1,1)], active:= fun x=> by rcases x with ⟨i,p⟩; cases p <;> simp,scoop:= fun x=> by rcases x with ⟨i,p⟩; cases p <;> simp, complete:= fun x i=> by rcases x with ⟨x,a⟩; rcases i with ⟨y,b⟩; cases b <;> fin_cases a<;> simp}
-- valuation.F flags prove by computing.Fl.Yes need parity grade ribbon syntax
lemma binary : (pack₂ I).flag (pairLip q)=q:=by
     letI : DecidableEq (I × Bool):= Classical.decEq _
     ext i; simp [Bloc.flag,pack₂]; have ht:Disjoint ({(i,false)}:Finset V) {(i,true)}:=by simp
     change Ribbon.shade _=q i; rw[← singleton_union, Bloc.gleam (pairLip q) _ _ ht,Ribbon.flavor, Ribbon.flavor]; simp [pairLip]
lemma trinary : (pack₃ I).flag (triple q)=q ∘ Prod.fst:=by
     letI : DecidableEq (I × Fin 3):= Classical.decEq _
     ext i; rcases i with ⟨i,t⟩; unfold Bloc.flag pack₃; cases t
     · let z:J:=(i,0); let b:J:=(i,1); simp
       have ht:Disjoint ({(i,(0:Fin 3))}:Finset J) {(i,1)}:=by simp
       rw[← singleton_union,Bloc.gleam (triple q) _ _ ht,Ribbon.flavor,Ribbon.flavor]; simp [triple]
     simp ; rw[Ribbon.flavor]; simp [triple]
-- eligibility: only incompat within same slot pair/c. either c chosen alone or any subset of pair. Same union formula from arbitrary s inj on tile projection. Prove every such supports.I. success.
def freeQ (I:Type)[Fintype I] :Set (Finset (I× Fin 3)):= {v | ∀ i, (i,2)∈v→ ∀ k∈v,k.1=i→ k.2=2}
lemma free₀: (∅:Finset J)∈ freeQ I:=by simp [freeQ]
lemma free₁(i:J):{i}∈freeQ I:=by rintro x h k hv hx; have he:i=(x,2):= (mem_singleton.mp h).symm; rw[mem_singleton] at hv; rw [hv,he]
lemma free_less (a b:Finset J)(h:a∈freeQ I)(hf:b⊆a): b∈ freeQ I:= fun i hi k hk=>h i (hf hi) k (hf hk)
open QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby.LifeT.SpinePlan.OrbitK.Duop
lemma free_all (s:Finset V)(hv:s∈ vines I)(v:Finset J)(h:v ⊆ (pack₃ I).plant s):v∈freeQ I:=by
     intro i hp j hj he
     let Q:=pack₃ I; have h1:(Q.unit_ (i,2))∈ s := (Q.belongs _ _).1 (h hp); have h2: Q.unit_ j∈ s:= (Q.belongs _ _).1 (h hj); have hh:Q.unit_ j=Q.unit_ (i,2):= (hv:Set.InjOn _ _) h2 h1 he; have hx: j.2=2:= decide_eq_true_iff.mp (congr_arg Prod.snd hh); exact hx
-- old sign price.K
end Eole.Triple
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Eole.Triple.free_all
#print axioms YM.MassiveQCD.Sample.Eole.Triple.binary
#print axioms YM.MassiveQCD.Sample.Eole.Triple.trinary
