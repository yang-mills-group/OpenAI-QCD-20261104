import YM.VMarker.Clause
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Twist
open QCD QCD.Grass QCD.Creek QCD.Lat Lattice Finset RG Wilson Ribbon Cupola Function Loom QCD.Cove
open MeasureTheory NormedSpace Filter
open Kites Ruby Finch Relight Plate Stew Stew.Phased Reggae
open scoped Topology BigOperators ContDiff Classical Matrix
variable {A B I E J K R U:Type}[Fintype I] {c:Side}{N:ℕ}
section pick
variable (q:A ↪ B)
noncomputable def clean {E:Type} (f:A→E)(g:B→E) := Function.extend q f g
lemma became {E:Type}(f:A→E)(g:B→E)(i:A) : clean q f g (q i)=f i:= q.injective.extend_apply ..
lemma other {E:Type}(f:A→E)(g:B→E)(x:B)(he:x∉Set.range q) : clean q f g x=g x:= by unfold clean Function.extend; rw [dif_neg]; exact he
lemma toggle (p:B→ Prop) (hQ:∀ i,p (q i)) (h:∀ i∉ Set.range q,p i) :∀ i,p i:=by
   intro i; by_cases he:i∈Set.range q; · obtain ⟨i,rfl⟩:=he; exact hQ i
   exact h i he
open Push.AbsoluteSums
variable (f:A→ℝ)
local notation "X"=> clean q f 0
lemma cleanNN (h:∀ i,0≤f i):∀ i,0≤ X i:= toggle q _ (fun i=> (became ..).symm ▸ h i) (fun i hi=> by rw [other _ _ _ _ hi]; exact le_rfl)
omit f in
lemma clean_budget (F:B→ℝ)(u:ℝ)(hv: 0≤F)(hf: Function.support F ⊆ Set.range q)(h:SumBudget (F∘q) u): SumBudget F u:= ⟨hv,(q.injective.summable_iff (f:=F) (fun _ hx=>by_contra fun h=> hx (hf h))).mp h.2.1, (q.injective.tsum_eq hf).symm.trans_le h.2.2⟩ -- order maybe support explicit complement.
end pick
structure Register (X: Rise c N E K)(F:Reel c N I R)(G:Film c N I U) where
    ear : R ↪ E
    tag : U ↪ K
    homeP i:X.row (ear i)= F.addr i
    mark i:X.front (tag i)= G.addr i
    freeP i:X.main (ear i)=0
    freeG i:X.plug (tag i)=0

end YM.MassiveQCD.Twist
