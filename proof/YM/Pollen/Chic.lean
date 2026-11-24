import YM.Pollen.Bills
import YM.Pollen.Taffy
import YM.TIPS.Stir
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical
variable {c f:Side}{n N j k F:ℕ}
open Onsite Tide QCD.Cove Creek
open Finset
open MassiveQCD MassiveQCD.Ribbon MassiveQCD.Cupola
variable {C:ℝ}{I:Type}[Fintype I]
variable {U:BudgetPoint}(o:I→Site c)(P0:I→Grid c→Lat.Fields c N→L[ℂ]Lat.Fields c N) (H:∀ i, Suit (o i) U C (P0 i))
local notation "X"=> Keys c N
local notation "S"=> Spine I
local notation "P" => Patio (Keys c N⊕Spine I)
local notation "q"=> traceI I
local notation "B!"=> burst q
include H
variable (a:I→ℂ)
set_option quotPrecheck false
local notation "Ω" p:arg=> actU (fun i=>P0 i p) (fun i=>(H i).bean p) a
open MassiveQCD.Sample.Quills
-- continuity only for allowed reads: preserve even though K publication might not itself continuous
variable (Q:Set (Finset I))(hv:∀ i∈Q,∀ j⊆i,j∈Q)(x:Grid c→ Patio (Keys c N ⊕ Spine I))(hvx:∀ V:Grid c, ValidPieces (Keys c N) (traceI I) univ (x V))(hf:∀ (i:Finset I),i∈ Q → Continuous (pluck (Keys c N) (burst (traceI I) i) ∘ x))
include hv hvx hf
set_option maxHeartbeats 640000 in
lemma riverX (s:List I):∀ i∈Q, Continuous (pluck X (burst q i) ∘ (fun p:Grid c=> (Ω p) s (x p))):=by
      induction s with
      | nil=> exact hf
      | cons j s ih=>
         let F:= fun p:Grid c=> (Ω p) s (x p); let K:= F; have he(V:Grid c): ValidPieces X (traceI I) univ (K V):=validpU _ _ a s (x V) (hvx V); intro i hi; let A:=pluck X (burst q i); let Hs:=shutter X i; let V:= univ.filter fun x=>x∈ (i.powerset:Set (Finset I));
         have h:Continuous (Hs∘ F):=by
              have h0: Hs∘F=fun x:Grid c=> ∑ j∈ V,Cupola.pick X (traceI I) j (F x):=by funext x; rw [Function.comp_apply,keen X (traceI I) _ _ (he _)]; unfold chop Cupola.slash; rw [_root_.sum_apply]; apply sum_congr _ (fun i h=>rfl); ext i; simp [V]
              rw [h0]; refine continuous_finsetSum _ fun j hj=>?_; have hp:j⊆ i:= mem_powerset.mp ((mem_filter.mp hj).2); let T':= pluck X (burst (traceI I) j); let B:=Cupola.pick X (traceI I) j; have hx:Continuous (T'∘F):= ih j (hv i hi j hp)
              let f:Grid c→ P:= B∘ F; have ht: Continuous fun p:Grid c=> (f p).val:= (stake X (burst (traceI I) j)).continuous.comp hx; exact ht.subtype_mk _
         let B p:= ((H j).bean p).dies (a j) j; let t:= fun p:Grid c=> if j∈ i then Hs (F p)+B p (Hs (F p)) else Hs (F p); have hg(p:Grid c): Hs ((Ω p) (j::s) (x p))=t p:=by rw [act_consU,map_add, Bean.restrict_at]; unfold t; split<;> first| rfl|simp; rfl
         suffices hX:pluck X (burst q i) ∘ (fun p=>(Ω p) (j::s) (x p)) = A∘ t by rw [hX]; refine A.continuous.comp ?_; unfold t; split; exact h.add (Suit.spendsC (a j) _ (H j) h); exact h
         funext p; let Z:=(Ω p) (j::s) (x p); change A Z=A (t p); rw [← hg p]; change pluck X (burst q i) Z= pluck X (burst q i) (Hs Z); unfold Hs shutter; rw [Cupola.pulse,Cupola.sensed,Finset.prod_eq_one,one_smul]; intro p hp; rw [if_pos hp]; simp
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.riverX
