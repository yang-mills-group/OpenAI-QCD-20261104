import YM.Gust.Storm
import YM.Gust.Turnp
import YM.Gust.Cav.Panes
set_option autoImplicit false
set_option maxHeartbeats 680000
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter MeasureTheory Analysis Tarn Tarn.Choir Tarn.Choir.Strip UV Mater Kind Gala
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix InnerProductSpace Classical
variable {K: Choir}{C: Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf: Foil P K T){m n k d:ℕ}{x:Points (m+1)}(hx:x∈conf _)(a:Axis)
local notation "F"=>Factory T n
local notation "S"=> polarM hK hf n
lemma Clouds(n:ℕ): (polarM hK hf n).Hierarchy := ⟨lawsB hK hf n,spinB hK hf n,passes hK hf n,reflectionP hK hf n,smoothP hK hf n,costs hK hf n⟩
-- D curtain. Letters staying. authentic.Q.
noncomputable def roamF (i:Fin (n+1))(v:Mater T n) : Mater T n where
       u:=v.u
       v:=update v.v i (K.arc a (v.v i))
       mem j:=by by_cases h:j=i; · subst j; rw [update_self,hue, arcing T hK hf a, (hue ..).1 (v.mem i),map_smul]
                 rw [update_of_ne h]; exact v.mem j
lemma roans (i:Fin (n+1))(w:Mater T n)(hu:Stay w d):Stay (roamF hK hf a i w) (d+1):=by
       intro j; change update w.v i (K.arc a (w.v i)) j∈ K.level (2*(d+1)); by_cases h:j=i; · subst i; rw [update_self, show 2*(d+1)=2*d+2 from (by omega)]; exact hK.graded _ _ _ (hu j)
       rw [update_of_ne h]; exact hK.slope (show 2*d≤2*(d+1) by omega) (hu _)
open Finset
noncomputable def leaps(n:ℕ): Stake T n→ₗ[ℂ]Stake T n:= Finsupp.linearCombination ℂ fun w=>∑ i:Fin (n+1), plant (roamF hK hf a i w)
lemma lives (w:Stake T n)(hu:w∈ Binds T d n):leaps hK hf a n w∈Binds T (d+1) n:=by
       induction hu using Submodule.span_induction with
       | mem v hv=> obtain ⟨w,h,rfl⟩:=hv; unfold plant leaps; rw [Finsupp.linearCombination_single,one_smul]; exact Submodule.sum_mem _ fun i _=> enter _ (roans hK hf a _ w h)
       | zero=> rw [map_zero]; exact Submodule.zero_mem _
       | add i j hi hj h k=> rw[map_add]; exact Submodule.add_mem _ h k
       | smul c i hi h => rw [map_smul]; exact Submodule.smul_mem _ _ h
variable (v:Fin m→Mater T n)(w:Mater T n)
include hK hf hx
lemma formation: HasDerivAt (fun z=> ValueP (Ward.cast x 0 a z) (Fin.cons w v)) (∑ i:Fin (n+1),ValueP x (Fin.cons (roamF hK hf a i w) v)) 0:=by
       let f(i:Fin (n+1)): Fin m→ K.W:=fun j=> (v j).v i; let L(r:K.W)(i:Fin (n+1))(y:Points (m+1)):= K.total _ y (Fin.cons r (f i)); let A(i:Fin (n+1))(z:ℝ):=L (w.v i) i (Ward.cast x 0 a z); let E(i:Fin (n+1)):=L (K.arc a (w.v i)) i x; let p:Fin (m+1)→Kind n:=Fin.cons w.u (fun i=> (v i).u); let c:= led (List.ofFn p); let B(i:Fin (n+1))(j:Fin (n+1)):= (roamF hK hf a i w).v j
       have h(i:Fin (n+1)):HasDerivAt (A i) (E i) 0:=Gust.deriv_head hK hx a _ _
       have hh(Y:Mater T n)(P:Points (m+1)): ValueP P (Fin.cons Y v)= led (List.ofFn (Fin.cons Y.u (fun i=> (v i).u)))*∏ i:Fin (n+1),L (Y.v i) i P:=by
            unfold ValueP; refine congr_arg₂ (· * ·) ?_ ?_; · congr 2; ext1 i; induction i using Fin.cases <;> rfl
            refine prod_congr rfl fun i _=> ?_; apply congr_arg; ext1 j; induction j using Fin.cases <;> rfl
       simp_rw [hh]; change HasDerivAt (fun z=> c * ∏ i,A i z) (∑ i:Fin (n+1), c*∏ j,L (B i j) j x) _
       apply ((HasDerivAt.fun_finsetProd (u:=Finset.univ) (fun i _=> h i)).const_mul c).congr_deriv
       simp_rw[mul_sum]; apply sum_congr rfl; intro i _; rw[← mul_prod_erase _ _ (mem_univ i)]
       rw [show L (B i i) i x= E i from (by unfold B roamF; simp only [update_self]; rfl), smul_eq_mul, mul_comm _ (E i)]; refine congr_arg (fun y=>c*(E i*y)) (prod_congr rfl (fun b hb=>?_)); unfold A B; dsimp only[roamF]; rw[update_of_ne (mem_erase.mp hb).1,Ward.start]
omit hx
variable (p:Fin m→Stake T n)(u:Stake T n)
include hx
lemma greatness_single : HasDerivAt (fun z=> valuation T n (m+1) (Ward.cast x 0 a z) (Fin.cons (plant w) p)) (valuation T n (m+1) x (Fin.cons (leaps hK hf a n (plant w)) p)) 0 :=by
      let y(z:ℝ) := Ward.cast x 0 a z; let A(z):= (valuation T n (m+1) (y z)).curryLeft (plant w); let B:=(valuation T n (m+1) x).curryLeft (leaps hK hf a n (plant w)); refine recurs (fun u=>HasDerivAt (fun z=> A z u) (B u) (0:ℝ)) ?_ ?_ ?_ ?_ p
      · intro q i h; simp_rw[MultilinearMap.map_coord_zero _ _ h]; exact hasDerivAt_const ..
      · intro p; have hh (q:Mater T n)(y:Points (m+1)) : (valuation T n _ y).curryLeft (plant q) (fun i=>plant (p i))=ValueP y (Fin.cons q p):=by
                  rw [MultilinearMap.curryLeft_apply,show Fin.cons _ _=fun i=>plant (Fin.cons (α:=fun _=>Mater T n) q p i) from funext fun i=> by induction i using Fin.cases <;> rfl]; exact values ..
        unfold A B; rw [show leaps hK hf _ n (plant w)= ∑ i, plant (roamF hK hf a i w) from (by unfold plant leaps; rw [Finsupp.linearCombination_single,one_smul]; rfl), map_sum,MultilinearMap.sum_apply]; simp_rw[hh]; exact formation hK hf hx a p w
      · intro q i u v h k; simp_rw [MultilinearMap.map_update_add]; exact h.add k
      · intro q i u h c; simp_rw [MultilinearMap.map_update_smul]; exact h.const_mul _
lemma greatness : HasDerivAt (fun z=> valuation T n (m+1) (Ward.cast x 0 a z) (Fin.cons u p)) (valuation T n _ x (Fin.cons (leaps hK hf a n u) p)) 0:=by
      let Fz(y:Points (m+1)):= (valuation T n _ y).curryLeft; change HasDerivAt (fun i=> Fz _ u p) (Fz _ _ p) _
      induction u using Mater.induced with
      | h=>simp only[map_zero]; exact hasDerivAt_const ..
      | hu i c=> simp_rw [map_smul]; exact (greatness_single hK hf hx a i p).const_mul _
      | ht x y h k=> simp_rw [map_add, MultilinearMap.add_apply]; exact h.add k
end YM.Massive.Gust
#print axioms YM.Massive.Gust.Clouds
#print axioms YM.Massive.Gust.greatness
