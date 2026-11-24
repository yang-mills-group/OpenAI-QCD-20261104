import YM.Gust.TopP
import YM.Gust.Satin
set_option autoImplicit false
set_option maxHeartbeats 560000
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter MeasureTheory Analysis Tarn Tarn.Choir Tarn.Choir.Strip UV Mater Kind Gala
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix InnerProductSpace Classical
variable {K: Choir}{C: Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf:Foil P K T){m n k:ℕ}{x:Points m}{y:Points k}(a:Axis)
variable (Y:Kernel.Gram fun z w:Visitors T a n=> gate (backward hK z.val a++w.val))
private lemma stemμ {I W:Type}[AddCommGroup W][Module ℂ W](m:ℕ)(R:(Fin m→ I)→ W):∃ F:MultilinearMap ℂ (fun _:Fin m=> I→₀ ℂ) W,∀ a:Fin m→ I,F (fun i=> Finsupp.single (a i) 1)=R a:=by
       induction m with
       | zero=>refine ⟨MultilinearMap.constOfIsEmpty ℂ (fun _:Fin 0=> _) (R Fin.elim0),fun i=>?_⟩; exact congr_arg R (Subsingleton.elim ..)
       | succ n ih=>
             choose G hG using fun i:I=> ih (fun p=>R (Fin.cons i p)); let h:= Finsupp.linearCombination ℂ G; refine ⟨LinearMap.uncurryLeft (M:=fun _=> I→₀ ℂ) h,fun a=>?_⟩; rw [LinearMap.uncurryLeft_apply]; unfold h; rw [Finsupp.linearCombination_single,one_smul]; exact (hG _ (Fin.tail a)).trans (congr_arg R (Fin.cons_self_tail _))
variable (hx:Clear x a)(hy:Clear y a)
noncomputable def crane (hx:Clear x a):= (stemμ m (fun u:Fin m→Mater T n=>Y.plant (tagged a u hx))).choose
lemma climbsT(u:Fin m→ Mater T n): crane hK a Y hx (fun i=>plant (u i))= Y.plant (tagged a u hx):= (stemμ m (fun u=>Y.plant (tagged a u hx))).choose_spec u
noncomputable abbrev crestM(x:Points m)(y:Points k)(a:Axis): Points (m+k):=points (Fin.append (fun i=> Ortho.move (Signed.reflect a) (x i.rev)) y.ofLp)
lemma meetT(u:Fin m→ Mater T n)(v:Fin k→ Mater T n):gate (backward hK (stageP u x) a++stageP v y) = ValueP (crestM x y a) (Fin.append (fun i=>tint hK a (u i.rev)) v):=by
       rw[← Gala.fit]; congr 1; unfold backward stageP; rw [← UV.Free.Lyre.reversesV (fun i:Fin m=>(x i,u i)),List.map_ofFn,← List.ofFn_fin_append]; apply congr_arg; funext i; cases i using Fin.addCases<;>simp [crestM]
noncomputable abbrev shadow (T:Pollens P K)(a:Axis)(n:ℕ): Stake T n →ₛₗ[starRingEnd ℂ] Stake T n:= (axisK hK (couture a) T n).comp (barK hK a T n)
lemma shimmer(x:Mater T n):shadow hK T a n (plant x)=plant (tint hK a x):=by simp [shadow,didD hK]
-- exact Gram on homogeneous single arrays.Swap.k.
variable (u:Fin m→ Stake T n)(v:Fin k→ Stake T n)
private lemma shells {α:Type*}(v:Fin m→α)(p:Fin k→α)(i:Fin k)(z:α): Fin.append v (update p i z) = update (Fin.append v p) (i.natAdd m) z:=by
       ext1 j; cases j using Fin.addCases with
       | left j=> rw [update_of_ne (show j.castAdd k ≠ i.natAdd m from by intro h; have he:=congr_arg Fin.val h; change j.val=m+i.val at he; omega)]; simp
       | right j=> by_cases h:j=i <;>simp[h]
private lemma shellT {α:Type*}(v:Fin m→α)(p:Fin k→α)(i:Fin m)(z:α): Fin.append (update v i z) p=update (Fin.append v p) (i.castAdd k) z:=by
       ext1 j; cases j using Fin.addCases with
       | left j=> by_cases h:j=i <;> simp[h]
       | right j=> rw [update_of_ne (show j.natAdd m ≠ i.castAdd k from by intro h; have he:=congr_arg Fin.val h; change m+j.val=i.val at he; omega)]; simp
lemma smoothRP(u: Fin m→ Stake T n)(v:Fin k→Stake T n): inner ℂ (crane hK a Y hx u) (crane hK a Y hy v) = valuation T n (m+k) (crestM x y a) (Fin.append (fun i=> shadow hK T a n (u i.rev)) v):=by
       let F:= valuation T n (m+k) (crestM x y a); let C':=crane hK a Y hx; let D:= crane hK a Y hy; let r:=shadow hK T a n; let G(p:Fin m→ Stake T n):=r∘ (p ∘ Fin.rev); change inner ℂ (C' u) (D v)= F (Fin.append (G u) v)
       apply recurs (fun u=> inner ℂ (C' u) (D v)= F (Fin.append (G u) v)) _ _ _ _
       · intro p i h; rw [C'.map_coord_zero i h, F.map_coord_zero (i.rev.castAdd k) (by simp[G,h]), inner_zero_left]
       · intro u; refine recurs (fun v=> inner ℂ (C' (fun i=>plant (u i))) (D v)= F (Fin.append (G (fun i=>plant (u i))) v)) ?_ ?_ ?_ ?_ _
         · intro p i h; rw [D.map_coord_zero i h,F.map_coord_zero (i.natAdd m) (by simp[h]), inner_zero_right]
         · intro v; have hh: Fin.append (G (fun i=>plant (u i))) (fun i=>plant (v i))= fun i=> plant (Fin.append (tint hK a ∘ u ∘Fin.rev) v i):=by ext1 j; cases j using Fin.addCases <;> simp[G, r, Mater.didD]
           unfold C' D F; rw [climbsT,climbsT,Y.measure,hh]; rw [values]; exact meetT ..
         · intro p i X V h k; rw [shells,D.map_update_add,inner_add_right,F.map_update_add, ←shells,←shells,h,k]
         intro p i X h c; rw [shells,D.map_update_smul, inner_smul_right,F.map_update_smul,←shells,h]; rfl
       · intro p i X Z h hk
         have hw(z:Stake T n) : G (update p i z)= update (G p) i.rev (r z):=turn_up p i z Fin.revPerm r -- fix
         rw [hw,shellT,map_add,F.map_update_add,C'.map_update_add,inner_add_left,← shellT,←shellT,←hw,←hw,h,hk]
       · intro p i X h c
         have hw(z:Stake T n) : G (update p i z)= update (G p) i.rev (r z):=turn_up p i z Fin.revPerm r
         rw [hw,shellT,map_smulₛₗ,F.map_update_smul,C'.map_update_smul, inner_smul_left, ←shellT, ←hw,h]; rfl
end YM.Massive.Gust
#print axioms YM.Massive.Gust.smoothRP
