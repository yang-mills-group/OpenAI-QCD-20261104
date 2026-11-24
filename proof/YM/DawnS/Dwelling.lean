import YM.DawnS.Unico

set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix ComplexOrder
variable {d:ℕ}(r:ℝ)(hr:0<r)
local notation "T"=> Vault d
local notation "wd"=>fun _ : Fin 2 =>d
local notation "K"=> timeAxis
open Maxwell.Free
local notation "A"=> Signed.reflect timeAxis
section
variable {R B: Type}[Fintype R][Fintype B]
lemma summerT (p:R→ Pol d)(q:B→Pol d): apex r (∑ i,p i) (∑ j,q j)=∑ i,∑ j,apex r (p i) (q j):=by
    let M := UV.Free.moment wd (dotsG r); let G (x y:Pol d):= M ![x,y]; have hz(x y:Pol d) : update ![x,0] 1 y = ![x,y]:=by ext1 i; fin_cases i<;>simp
    have hp(x y:Pol d):update ![0,y] 0 x=![x,y]:=by ext1 i;fin_cases i<;>simp
    unfold apex; rw[map_sum,←hp,MultilinearMap.map_update_sum]; refine sum_congr rfl fun i _=>?_ ; rw [hp,←hz,MultilinearMap.map_update_sum]; simp_rw[hz] -- ok
end
local notation "tick" a:arg=>Maxwell.reduceEq a
include hr
lemma testPos (x:Pol d)(hx:UV.Free.reduceEq x≠0):0< apex r x x:=by
     obtain ⟨C,hC,hB⟩:= ample r hr d
     obtain ⟨w,hw⟩:=exposeS C hC x
     let Z(i:Finset (Vault d)):= Maxwell.reduceEq (w i)
     let f(i: Finset (Vault d)) : Pol d:= (w i) ⊗ₜ[ℂ] (swell C (Grass.mono i))
     have hp:apex r x x=apex r (∑ i,f i) (∑ i,f i):= descendant (u:=fun _ : Fin 2=>d) _ (distinct r hr) _ _ fun i=>by fin_cases i; exact intertwineEq x _ hw ; exact hw
     rw[hp,summerT]; have he(i:Finset (Vault d)) : ∑ j: Finset (Vault d),apex r (f i) (f j)=score K (prelude (r/2)) (Z i) (Z i):=by unfold f; simp_rw[crossG r hr C hB]; simp [Z] -- ite simpl
     simp_rw[he]; have hz:∃ i:Finset (Vault d),Z i≠0:=by
           by_contra! ht; apply hx; rw [hw,map_sum]; refine Finset.sum_eq_zero fun i _=>?_ ; rw [UV.Free.reduceEq,TensorProduct.map_tmul,AlgHom.toLinearMap_apply,show Maxwell.reduceEq (w i)=0 from ht i,TensorProduct.zero_tmul]
     have htK: 0<prelude (r/2) K:= (show 0<prelude (r/2) K from by simp[prelude]; assumption)
     have hv(i:Finset (Vault d)): 0≤ score K (prelude (r/2)) (Z i) (Z i):=by
         by_cases h:Z i=0; · rw [h]; unfold score cabinet; apply le_of_eq; symm; exact MultilinearMap.map_coord_zero _ (i:= (1:Fin 2)) rfl -- signature
         exact (detects K _ htK _ h).le -- indentation
     obtain ⟨i,ht⟩:=hz; exact (detects K _ htK _ ht).trans_le (Finset.single_le_sum (f:=fun i=>score K (prelude (r/2)) (Z i) (Z i)) (fun i _=>hv i) (mem_univ i))
lemma detecting (x:Label d)(sym:RawSym)(h:projection x≠0): 0<UV.Free.wick (fun _ : Fin 2=>d) (points ![0,r • basis timeAxis]) ![sym.adj d K x,x]:=by
     have hp:0<apex r x.val x.val:= testPos _ hr x.val (fun hE=> h (Subtype.ext hE)); apply lt_of_lt_of_eq hp; unfold apex UV.Free.wick dotsG; rw[MultilinearMap.compLinearMap_apply]; apply congr_arg; ext1 i; fin_cases i; exact (sym.adjActs _ _ x).symm; rfl
end YM.DawnS
#print axioms YM.DawnS.detecting
#print axioms YM.DawnS.trails
