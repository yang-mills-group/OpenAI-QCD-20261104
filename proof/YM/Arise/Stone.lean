import YM.Arise.Rex
import YM.Push.RELAY_MARK.Current
/-! # Arc gives EXACT linear gauge slot in horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise
open Function Lattice Finset Wilson Filter MeasureTheory Tensor Work.G06 RG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {r n m i j k d:ℕ}
variable {F M:Type*}[NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup M][NormedSpace ℝ M]
variable {G: Gauge}(s: Signed)(x y:Cover)(a b:Axis)(p:PlaqAxes)
variable (z: Cover)(l: List Axis)
open Labels Source Source.Drops Work.G03
local notation "g⋆"=> G.Color
lemma net_pla (A: Taylor G k)(x:E4): net A p.val.1 p.val.2 x 1=zoom (some p) (diagonal (Maxwell.takeCurl A p.val.1 p.val.2)) x:=by
     let a:=p.val.1; let b:=p.val.2; let A1:= Maxwell.grad a (A.value b); let B1:=Maxwell.grad b (A.value a); let Y(v w:ℝ):= x+(v • basis a+w • basis b)
     have hh:meanPartial A a b x 1=ameet p A1 x:=by
          unfold meanPartial ameet; simp_rw [one_mul,add_assoc]; rw [swapA (fun i j=> Maxwell.grad a (A.value b) (x+(i • basis b+j • basis a))) (show Continuous _ from (continuous_grad ..).comp (show Continuous fun v:ℝ×ℝ=> x+(v.1 • basis b+v.2 • basis a) by fun_prop))]; simp_rw [show ∀ i j:ℝ,i • basis b+j • basis a=j • basis a+i • basis b from fun i j=> add_comm _ _]; rfl
     have ht:meanPartial A b a x 1=ameet p B1 x:=by unfold meanPartial ameet; simp_rw [one_mul,add_assoc]; rfl
     change meanPartial _ a b _ _-meanPartial _ b a _ _=_; rw [hh,ht]; rw [Maxwell.takeCurl_diag]; change zoom (some p) A1 x-zoom (some p) B1 x= _; rw [show Maxwell.grad _ _- Maxwell.grad _ _=A1+(-1:ℝ) • B1 from by rw [neg_one_smul]; rfl, zoom_add,zoom_smul]; simp [sub_eq_add_neg]
     · exact continuous_grad ..
     exact Continuous.const_smul (continuous_grad A b a) _
variable (w:Rhythm)(L:F→L[ℝ]M)
lemma mixH (f:Walk→F) : L (hears f w)= hears (L∘ f) w:=by induction w using Finsupp.induction_linear with |zero=>simp|add u v h hp=>rw [map_add,map_add,map_add,h,hp]|single i a=> simp [hears]
lemma signsSum {I:Type*}(g:Finset I)(f:I→Walk→F): hears (∑ i∈g,f i) w=∑ i∈g, hears (f i) w:=by induction w using Finsupp.induction_linear with |zero=>simp|add u v h hp=>simp_rw [map_add,h,hp,sum_add_distrib]|single i a=>simp only [hears,Finsupp.linearCombination_single,Finset.sum_apply, smul_sum]
section
variable [CompleteSpace F][CompleteSpace M]
lemma zoomLin (f:E4→F)(h:Continuous f)(z:E4): L (zoom (some p) f z)=zoom (some p) (L∘f) z:=by
   unfold zoom ameet; rw [← L.intervalIntegral_comp_comm ((rot_s p f z h).intervalIntegrable ..)]; congr 1; ext1 s; rw [← L.intervalIntegral_comp_comm (f:=fun r:ℝ=> f (z+(s • basis p.val.1+r • basis p.val.2))) ((show Continuous _ from h.comp (show Continuous (fun r:ℝ=> z+(s • basis p.val.1+ r • basis p.val.2)) by fun_prop)).intervalIntegrable (μ:=volume) 0 1)]; rfl
end
lemma watch (k:G.ColorIndex)(A:Taylor G l.length)(hL:l.length≤d): (hears (fun u:Walk=>net A p.val.1 p.val.2 (gross (stop 0 u)) 1) (chore d l p)) k=l.length.factorial • (Maxwell.takeCurl A p.val.1 p.val.2 (basis ∘ l.get)) k :=by
     let Q:g⋆ →L[ℝ]ℝ:= EuclideanSpace.proj k; let M:=Maxwell.takeCurl A p.val.1 p.val.2; have he:Tensor.Sym M:=(Maxwell.closedCurl A).coeffSym p.val.1 p.val.2; let X: Lore ℝ l.length:=⟨Q.compContinuousMultilinearMap M, (fun x hu=> congr_arg Q (he x hu))⟩; change Q (hears _ _)=_; rw [mixH]; let W:=zoom (some p) (diagonal X.val)
     have h : (fun u:Walk=> Q (net A p.val.1 p.val.2 (gross (stop 0 u)) 1))= (W ∘ gross) ∘ (stop (0:Cover)):=by funext u; rw [net_pla,zoomLin p Q _ (diag_smooth M ∞|>.continuous)]; rfl
     change hears (fun u:Walk=> Q _) _= _; rw [h,← hearth]; change stare (some p) _ _ X=_; rw [received _ _ _ _ (per_goal l p hL)]; exact accommodate (.some p) l X.val X.property _
lemma watch_n (k:G.ColorIndex)(A: Taylor G i)(hp:i ≠ l.length)(ht:i ≤ d)(hL:l.length≤d): (hears (fun u:Walk=> net A p.val.1 p.val.2 (gross (stop 0 u)) 1) (chore d l p)) k=0:=by
     let Q:g⋆ →L[ℝ]ℝ:= EuclideanSpace.proj k; let M:=Maxwell.takeCurl A p.val.1 p.val.2; have he:Tensor.Sym M:=(Maxwell.closedCurl A).coeffSym p.val.1 p.val.2; let X: Lore ℝ i:=⟨Q.compContinuousMultilinearMap M,(fun v u=> congr_arg Q (he v u))⟩; change Q (hears _ _)=_; rw [mixH]; let W:=zoom (some p) (diagonal X.val)
     have h : (fun u:Walk=> Q (net A p.val.1 p.val.2 (gross (stop 0 u)) 1))=(W ∘ gross) ∘ (stop (0:Cover)):=by funext u; rw [net_pla,zoomLin p Q _ (diag_smooth M ∞|>.continuous)]; rfl
     change hears (fun u:Walk=> Q _) _=_; rw [h,← hearth]; change stare (some p) _ _ X=_; rw [rests _ _ _ _ (per_goal l p hL) ht hp.symm]; rfl
lemma gauge_t (n:ℕ)(A:Snap G n) (H:Source.Hol G)(ht:Drops.Peg H n)(hL:l.length≤d)(h:n≤d)(i:G.ColorIndex) : (hears (fun w:Walk=> Blurb H n ⟨w,p⟩ A) (chore d l p)) i=l.length.factorial • (Maxwell.takeCurl (expand n A l.length) p.val.1 p.val.2 (basis ∘ l.get)) i:=by
    let f(k:ℕ)(u:Walk):= net (expand n A k) p.val.1 p.val.2 (gross (stop 0 u)) 1; rw [show (fun w:Walk=> Blurb H n ⟨w,p⟩ A)= ∑ i∈range (n-1),f i from (funext fun u=>by rw [Finset.sum_apply,ht.initial]; exact Push.Mark.samples ..),signsSum]; by_cases hp:l.length<n-1; · change (∑ k∈range (n-1), hears (f k) (chore d l p):g⋆) i=_; rw [show (∑ k∈ range (n-1), hears (f k) (chore d l p):g⋆) i= ∑ k∈range (n-1),(hears (f k) (chore d l p):g⋆) i from map_sum (EuclideanSpace.proj (𝕜:=ℝ) i) (fun k=> hears (f k) _) _,sum_eq_single_of_mem l.length (mem_range.mpr hp)]; exact watch p l i _ hL; intro k hk h; exact watch_n p l i _ h (by rw [mem_range] at hk; omega) hL
    rw [show expand n A l.length=0 from dif_neg hp]; rw [sum_eq_zero]; simp [Maxwell.takeCurl]
    intro k hk; ext b; exact watch_n p l b _ (by rw [mem_range] at hk; omega) (by rw [mem_range] at hk; omega) hL
end YM.Arise
#print axioms YM.Arise.gauge_t
