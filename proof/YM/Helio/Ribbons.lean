import YM.Helio.Gate
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
variable {Γ:Silo c}{A: BankP c}{U:St c}
namespace Meridian
local notation "Mα" α:arg=> wheelS (rplus c α)
variable (α:Axis)(d:Tick c)
lemma coverMapC : ((Mα α) d).2.2=d.2.2.image (act (rplus c α)):=congr_arg Prod.snd (congr_arg Prod.snd (trill (rplus c α) d))
lemma stripSize (X Y: Support c)(x y:Site c)(hx:x∈X)(hy:y∈Y)(h:separation x y ≤1)(M:ℕ):coverNumber M (X∪Y) ≤ coverNumber M X+coverNumber M Y:=by
  obtain ⟨A,⟨a1,a2⟩,ha⟩ := coverNumber_realized M X
  obtain ⟨B,⟨b1,b2⟩,hb⟩ := coverNumber_realized M Y
  have la : halo M A ⊆ halo M (A∪B) := Corona.halo_mono le_rfl (fun i hi => Finset.mem_union_left B hi)
  have lb : halo M B ⊆ halo M (A∪B) := Corona.halo_mono le_rfl (fun i hi => Finset.mem_union_right A hi)
  have ht (i) (hi : i∈halo M (A∪B)) : Relation.ReflTransGen (Corona.Touch (halo M (A∪B)) 1) x i :=by
    obtain ⟨j,hj,hz⟩ := halo_spec.mp hi
    rcases Finset.mem_union.mp hj with he|he
    · exact Corona.grow la (a2 _ (a1 hx) _ (halo_spec.mpr ⟨_,he,hz⟩))
    exact (show Relation.ReflTransGen (Corona.Touch (halo M (A∪B)) 1) x y from (.single ⟨la (a1 hx),lb (b1 hy),h⟩)).trans (Corona.grow lb (b2 _ (b1 hy) _ (halo_spec.mpr ⟨_,he,hz⟩)))
  apply le_trans _ (le_trans (Finset.card_union_le A B) (ha ▸ hb ▸ le_rfl))
  apply Corona.list_cost
  refine ⟨fun i hi => ?_, fun i hi j hj => (Corona.sym (ht _ hi)).trans (ht _ hj)⟩
  rcases Finset.mem_union.mp hi with he|he
  · exact la (a1 he)
  exact lb (b1 he)
lemma spectral (B:ℕ): coverNumber B ((Mα α) d).2.2= coverNumber B d.2.2:=by rw [coverMapC, Push.Local.cover_map (act (rplus c α)) (Push.Local.turn_sep _ _)]
lemma stripC (h:fertile d)(M:ℕ):coverNumber M (strip α d)≤ coverNumber M d.2.2*2:=by
    let S:= rplus c α; let p:=d.1+step α; have hh:p∈ ((Mα α) d).2.2:=by rw [risesT α d]; exact mem_image_of_mem _ h.1
    calc
      _ ≤ _:= stripSize _ _ d.1 p h.1 hh (show separation d.1 p≤1 by rw [separation_comm,separation]; unfold p; rw [add_comm,add_sub_cancel_right]; exact pdist_step _) M
      _ = _:=by rw [spectral α d]; omega
lemma scripture : fertile d ↔ fertile ((Mα α) d):=by rw [trill]; unfold fertile; simp
noncomputable def basePrice (A:BankP c)(α:Axis)(d:Tick c):ℝ:= silos A d+silos A ((Mα α) d)
lemma footA (P:Run.Pack id id η δ B U q Γ A)(x:Site c) : Anchored (fun i: {i:Tick c//fertile i} => i.val.1) (fun i=>basePrice A α i.val) (fun i=>coverNumber B i.val.2.2) δ (q+q):=by
    let F i:= Run.rent δ B (i:Tick c).2.2*silos A i; have hx i:0 ≤ F i:=mul_nonneg (Run.fair ..).le (need P i)
    let X:={i:Tick c//fertile i}; intro y; let g (i:Tick c):= if i.1=y then F i+F ((Mα α) i) else 0
    have hq : (fun i:X=> if i.val.1=y then basePrice A α i.val * Real.exp (δ*coverNumber B i.val.2.2) else 0)= fun i=> g i.val:=by
         funext i; change _= ite _ _ _; split; next H=> unfold basePrice F Run.rent; rw [spectral]; ring
         next _=>rfl
    rw [hq]; have ht(i):0 ≤ g i:=ite_nonneg (add_nonneg (hx i) (hx _)) le_rfl
    have hK (t:Site c):SumBudget (fun i:Tick c=> if i.1=t then F i else 0) q:=by
       refine ⟨fun i=> ite_nonneg (hx i) le_rfl,Summable.of_finite,?_⟩; rw [tsum_fintype]; unfold Tick; simp only [Fintype.sum_prod_type]; rw [sum_eq_single t]; swap
       · intro i _ hi; simp [hi]
       rotate_right; · simp
       simp only [ite_true]; exact P.spends t
    have hf(i:Tick c) : g i=(if i.1=y then F i else 0)+(if ((Mα α) i).1=y+step α then F ((Mα α) i) else 0):=by unfold g; rw [risesT]; simp only [add_left_inj]; split_ifs <;> simp
    have hV : SumBudget g (q+q):= (funext hf).symm ▸ budget_plus (hK y) (budget_pull _ (Mα α).injective (hK (y+step α)))
    exact budget_pull Subtype.val Subtype.val_injective hV
end Meridian
end YM.QCD.Entr
#print axioms YM.QCD.Entr.Meridian.footA
