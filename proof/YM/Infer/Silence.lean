import YM.Infer.Shack
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise ContDiff Stamp Kronecker Classical
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit Patria Exposure
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace Gallery
open QCD.Kites PrismD Civic
open Romance
local notation "V"=> Lat.Fields n 6
local notation "Fω"=> Insertion n 6
variable (x:Drape)(l:List Axis)(Q:BudgetPoint)(z:ℝ)
variable {p:Label d}(Y: SourceRead.TaperHol)(W:Knot p)(h:Requisite Y p W)
open Depth Canvas Poised Cylinder
variable {I:Type}(H:I→ Insertion n 6)(X Y:I→Insertion n 6)(T:I→Set (Site n))
-- at any position. H k true replacement term. Comparison H X others nuclear. Ded induction avoiding expansion spices.
variable (u:List I)(p:I→Bool)
local notation "Φ"=> P.average
lemma lists_f {l:List I}{S:Set (Site n)}(h:∀ i∈l,Floors S (Y i)): Floors S (l.map Y).prod:=by
    induction l with|nil=>exact flooring_one| cons i l ih=>exact flooring_mul (h i (by simp)) (ih (fun j hj=> h j (List.mem_cons_of_mem _ hj)))
lemma floors_sub {x y :Insertion n 6}{S:Set (Site n)}(h:Floors S x)(hp:Floors S y):Floors S (x-y):=by rw [sub_eq_add_neg,← neg_one_smul ℂ y]; exact flooring_add h (flooring_smul _ hp)
lemma still_array (p:I→Bool)(hq:u.Nodup)(ht:∀ i,NullOn P (H i) (T i))(hp:∀ i, Gallery.moon (p i) (H i))(he:∀ i j,i≠j→Floors (T j) (H i)∧ Floors (T j) (X i)):
 ‖Φ (u.map X).prod‖= ‖Φ (u.map (fun i=>H i-X i)).prod‖ := by
     let Y:= fun i=>H i-X i; have h(l:List I)(hl:l.Nodup)(x: Insertion n 6)(hx:∀ i∈ l,Floors (T i) x) : ‖Φ (x*(l.map X).prod)‖= ‖Φ (x*(l.map Y).prod)‖:=by
        induction l generalizing x with
        | nil=> rfl
        | cons i l ih=> obtain ⟨hi,hL⟩:= List.nodup_cons.mp hl
                        let S:=T i; let z:= (l.map X).prod; have hb:z=z:=rfl; have hV:Φ (x*H i*z)=0:=by
                           rw [balance (hp i), mul_assoc]; refine ht i _ (flooring_mul ?_ (lists_f _ (fun j hj=> (he j i (fun h=>hi (h ▸ hj))).2))); have hf := hx i (by simp); split; exact gradedF hf; exact hf
                        have hz:Φ (x*Y i*z)= - Φ (x*X i*z):=by unfold Y; rw [mul_sub,sub_mul,map_sub,hV,zero_sub]
                        rw [List.map_cons,List.prod_cons,List.map_cons,List.prod_cons, ←mul_assoc,←mul_assoc]; change ‖Φ (x*X i*z)‖= _; rw [←norm_neg, ← hz]; apply ih hL; intro j h; have hs:= he i j (fun hv=> hi (hv.symm ▸ h)); exact flooring_mul (hx j (List.mem_cons_of_mem _ h)) (floors_sub hs.1 hs.2)
     simpa only [one_mul] using h u hq 1 (fun _ _=> flooring_one)
-- disjoint criterion on any constellation
variable (r k m:ℕ)
lemma beyondS (x y:Site n)(h:k+r < separation x y): rim k x⊆ Outer r y:=by
     intro z hz; change r < separation z y; change separation x z ≤ k at hz; have hp := separation_triangle x z y; omega
lemma spins_array (p:I→Bool)(b:I→ Cover)(hs:∀ i j,i≠j→ k+r < separation (wrap n (b i)) (wrap n (b j))) (h:u.Nodup)(ht:∀ i,NullOn P (H i) (Outer r (wrap n (b i))))(hp:∀ i,Gallery.moon (p i) (H i))(hx:∀ i, Floors (rim k (wrap n (b i))) (H i) ∧ Floors (rim k (wrap n (b i))) (X i)) : ‖Φ (u.map X).prod‖= ‖Φ (u.map (fun i=>H i-X i)).prod‖:=by apply still_array P H X _ u p h ht hp; intro i j hh; exact ⟨lower_maps (hx i).1 (beyondS _ _ _ _ (hs i j hh)),lower_maps (hx i).2 (beyondS _ _ _ _ (hs i j hh))⟩
end Gallery
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.Gallery.spins_array
