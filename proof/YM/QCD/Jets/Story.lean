import YM.QCD.Jets.Avenue
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets.Sun
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v:ℝ}{l:ℕ}{G:Flight j k}{h:f.val=c.val*G.L.val}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "R"=> Junta c f F
local notation "S"=> sliceL G h
variable {T:Grid f→Sheet f}(P:Sun G c f h δ v q u a l T)

lemma pony (W:Finset (Support f)) (U:Grid f): ∑ j∈W, pond (ha c f F) (ship P.X j (settled U))=pond (ha c f F) (∑ j∈W,ship P.X j (settled U)):=by
    induction W using Finset.induction_on with
    | empty=> rw [sum_empty,sum_empty]; unfold pond; symm; apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j _; exact zero_smul ℂ (_:EndA R)
    | insert i s hi ih=> rw [sum_insert hi,sum_insert hi]; rw [show ha c f F=head A B from rfl,pond_add, ← show ha c f F=head A B from rfl, ih]
lemma bank (W:Finset (Support f))(U:Grid f)(r:ℕ):∑ i ∈ W,bark (longP P.Z P.V r (settled U) i)=bark (∑ i∈W,longP P.Z P.V r (settled U) i : Water c f F):=by induction W using Finset.induction_on with
  | empty=> rw [sum_empty,sum_empty]; unfold bark barkG; symm; apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j _; exact zero_smul ℂ (_:EndA R)
  | insert i W hi ih=> rw [sum_insert hi,sum_insert hi,ih]; exact (barkSum _ _).symm

lemma podium (U:Grid f): (∑ j,ship P.X j (settled U): Matrix A A ℂ)=(copies F (T U))⁻¹:=by
   rw [← Jets.linked _ _ (P.stable.sole U)]; ext a b; rw [Matrix.sum_apply]; simp_rw [hook_eq]; have he:=P.X0.sells a.1.1 b.1.1 U; change _=if a.2=b.2 then _ else _; split
   next h=> rw [← Matrix.sum_apply]; rw [he]; rfl
   next h=> simp only [h,if_false,sum_const_zero]

lemma prove_sums {I:Type*}(W: Finset I) [DecidableEq I](w:Finset I)(H : I→Bundle)(i j:Fiber)(h:w⊆W): ∑ k ∈ W,(if k∈ w then H k else 0) i j=(∑ k∈ w,H k) i j:=by
  rw [Matrix.sum_apply]; symm; calc
   _ = ∑ k∈ w,(if k∈w then H k else 0) i j:=sum_congr rfl fun k hk=>by rw [if_pos hk]
   _ = _ :=sum_subset h (fun k hk hm=>by rw [if_neg hm]; rfl)

lemma salt (U:Grid f)(r:ℕ): short P.Z P.V r (settled U) +∑ i,longP P.Z P.V r (settled U) i=bladesF ((copies F (T U))⁻¹*(ater G h U)ᴴ) (ater G h U*(copies F (T U))⁻¹):=by
  rw [← Jets.linked _ _ (P.stable.sole U)]; unfold ater; rw [←choir_star, show copies F (T U)⁻¹=choir F (T U)⁻¹ from rfl,← choir_mul,← choir_mul]; ext a b
  simp only [Matrix.add_apply,Matrix.sum_apply]; unfold short longP; cases a <;> cases b
  next a b=>
    simp only [foamI]; change _= if a.2=b.2 then _ else _; split
    next hx=>
     rw [prove_sums _ _ _ _ _ (subset_univ _)]
     exact congrFun (congrFun (show spoon P.Z _ r a.1.1 b.1.1 (settled U)+(∑ x∈ satZip a.1.1 r, P.Z a.1.1 b.1.1 x (settled U)) = cell (rightL G h T U) a.1.1 b.1.1 from (produce P.Z0 _ _ _ _ U).symm) a.1.2) b.1.2
    next hx=> simp only [sum_const_zero,add_zero]
  next=> simp only [foamLR,sum_const_zero,add_zero]; rfl
  next=> simp only [foamRL,sum_const_zero,add_zero]; rfl
  next a b=>
    simp only [foamR]; change _= if b.2=a.2 then _ else _; split
    next hx=>
     rw [prove_sums _ _ _ _ _ (subset_univ _)]
     exact congrFun (congrFun (show spoon P.V _ r b.1.1 a.1.1 (settled U)+(∑ x∈ satZip a.1.1 r, P.V b.1.1 a.1.1 x (settled U)) = cell (leftL G h T U) b.1.1 a.1.1 from (produce P.V0 _ _ _ _ U).symm) b.1.2) a.1.2
    next hx=> simp only [sum_const_zero,add_zero]

lemma committed (F r:ℕ): (P.equip F r).Cast (ater G h) (fun U=> copies F (T U)):=by
 letI : NormedAlgebra ℚ (EndA (Junta c f F)):= .restrictScalars ℚ ℂ _
 intro U; change birth (∑ i: Support f ⊕ Support f,mapQ P.X P.Z P.V r i (settled U))=_; rw [Fintype.sum_sum_type,add_comm]
 simp only [mapQ, Sum.elim_inr,Sum.elim_inl,pony,bank,podium]; rw [show (∑ i,longP P.Z P.V r (settled U) i)=_ from eq_sub_of_add_eq' (salt (F:=F) P U r)] -- signature
 exact exp_add_of_commute (Commute.symm (pondB ..))
end YM.QCD.Jets.Sun
