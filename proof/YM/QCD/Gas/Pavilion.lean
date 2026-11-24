import YM.QCD.Gas.Ray
import YM.Push.ABSOLUTE_SUMS.Absence
/-! # cluster atlas with bounded arms. Useful both with omitted words and full. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.GasP
open Push.AbsoluteSums Partition Relation Graph Ursell Finset Gas Function RG Lattice Wilson
open scoped BigOperators Classical Topology
variable {ι K : Type*} [NormedCommRing K][NormOneClass K] [NormedAlgebra ℚ K] [NormedAlgebra ℝ K][CompleteSpace K]
variable {n: Side}{p: ι→Support n}{w:ι→K}{g:ι→ℝ}{a c t u:ℝ}{M:ℕ}
def omission (p:ι → Support n)(w:ι→K)(W:Support n)(i:ι):= if Disjoint W (p i) then w i else 0
def leave (p:ι → Support n) (w:ι→K) (W:Support n) (i:Clusters ι):= if Disjoint W (unionOf p i.2) then 0 else termP (blocked p) w i
lemma odds (W:Support n)(i:Clusters ι): termP (blocked p) (omission p w W) i=termP (blocked p) w i-leave p w W i:=by
   unfold leave; split
   next h=>
      rw [sub_zero]; unfold termP; congr 2; refine prod_congr rfl fun j _=>?_ ; exact if_pos (h.mono_right (subset_biUnion_of_mem (p∘i.2) (mem_univ _)))
   next h=>
      obtain ⟨z,hz,he⟩:=not_disjoint_iff.mp h; obtain ⟨j,hj,he⟩:=mem_biUnion.mp he
      rw [sub_self,termP, prod_eq_zero hj (show omission p w W (i.2 j)=0 from if_neg (not_disjoint_iff.mpr ⟨_,hz,he⟩)),smul_zero,smul_zero]
lemma foyer {Y:ι→ℝ}(h : ∀ i,0≤ Y i)(hv:Trees.Ready p M g a c t u)(he:∀ i,Y i ≤ g i): Trees.Ready p M Y a c t u:=⟨hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,h, Labels.raise_prices _ _ h hv.2.2.2.2.2 he⟩
lemma portage (hp : ∀ i,(p i).Nonempty)(h:Trees.Ready p M g a c t u)(he:∀ i, ‖w i‖≤g i)(ha:0≤a)(W:Support n):
    let l:=leave p w W
    let O:= omission p w W
    Summable (fun i=> ‖l i‖) ∧ Summable (termP (blocked p) w) ∧ Summable (valueP (blocked p) O) ∧ NormedSpace.exp (logS (blocked p) w) *NormedSpace.exp (-∑' i,l i) = totalP (blocked p) O :=by
   intro l O
   let Q:= blocked p; have hH:=literal_test p hp
   have ht:Hard Q := ⟨fun i=>Or.inl rfl, fun _ _=> blocked_back p⟩
   have hv :∀ i, ‖O i‖≤g i:=by
      intro i; unfold O omission; split; exact he i; rw [norm_zero]; exact h.2.2.2.2.1 i
   obtain ⟨hg,hx,hB⟩:= GasP.price_log _ w ht _ _ hH ha (foyer (fun _=> norm_nonneg _) h he)
   obtain ⟨h₁,h₂,h₃⟩:= GasP.price_log _ O ht _ _ hH ha (foyer (fun _=> norm_nonneg _) h hv)
   have hL : Summable fun i=> ‖l i‖ := by
     refine hx.2.1.of_nonneg_of_le (fun i=> norm_nonneg (l i)) (fun i=> ?_) -- desired norm? syntax
     unfold l leave; split; next _=> rw [norm_zero]; exact norm_nonneg _
     next _=> exact le_rfl
   refine ⟨hL,hx.2.1.of_norm,h₁.2.1.of_norm,?_⟩
   rw [← h₃, show logS (blocked p) O=logS Q w-∑' i,l i from ?_, sub_eq_add_neg,NormedSpace.exp_add]
   unfold O logS; simp_rw [odds]; exact hx.2.1.of_norm.tsum_sub hL.of_norm

def portion (p:ι→Support n)(w:ι→K)(W:Support n):K:= ∑' i:Clusters ι, if unionOf p i.2=W then termP (blocked p) w i else 0
lemma departures (W:Support n) (h: Summable (fun i=> ‖termP (blocked p) w i‖)) :
    ∑ T:Support n,(if Disjoint W T then 0 else portion p w T)= ∑' i, leave p w W i:=by
   let f (T:Support n)(i:Clusters ι):=if unionOf p i.2=T then leave p w W i else 0
   have he T: Summable fun i=> f T i:= by
      refine Summable.of_norm (h.of_nonneg_of_le (fun _=> norm_nonneg _) fun i=>?_)
      unfold f leave; split <;> first | exact norm_zero.trans_le (norm_nonneg _) | skip
      split; next _=> exact norm_zero.trans_le (norm_nonneg _)
      next _=> exact le_rfl
   have hv (T:Support n): ∑' i,f T i=if Disjoint W T then 0 else portion p w T:=by
      split
      next h=>
         have hf (i):f T i=0:=by
            unfold f leave; split
            next he=> rw [if_pos (show Disjoint W _ from he.symm ▸ h)]
            next _=> rfl
         simp only [hf,tsum_zero]
      next h=>
         refine tsum_congr fun i=>?_ ; unfold f leave; split
         next he=> rw [if_neg (fun hh=>h (he ▸ hh))]
         next _=> rfl
   rw [← tsum_congr (f:=fun i=> ∑ T,f T i) (g:=leave p w W) (fun i=> by unfold f; rw [sum_ite_eq,if_pos (mem_univ _)]), Summable.tsum_finsetSum (s:=univ) (fun i _=> he i)]; exact sum_congr rfl fun i _=> (hv i).symm
lemma term_bill (h:∀ i, ‖w i‖≤g i)(z:Clusters ι): ‖termP (blocked p) w z‖ ≤ clusters (blocked p) g z.2:=by
   apply (normStep (blocked p) w z).trans
   rw [Gas.term_nonneg]; simp only [norm_norm]; unfold clusters; gcongr; exact h _
-- bundle mass
variable {α :Type*}[DecidableEq α]
def Cap (h: ι→ℝ)(p:ι→α) (x:α):ℝ:= ∑' i, if p i=x then h i else 0
lemma hat_nonneg (h:ι→ℝ) (p:ι→α) (hh:∀ i,0≤h i) (x:α): 0≤Cap h p x:=tsum_nonneg (fun i=> ite_nonneg (hh i) le_rfl)
lemma somG {k: ι→K}{p:ι→α}(h : Summable fun i=> ‖k i‖)(x:α): Summable fun i=> if p i=x then k i else 0:=by
   refine Summable.of_norm (h.of_nonneg_of_le (fun i=> norm_nonneg _) fun i=>?_); split; next _=> exact le_rfl
   next _=> exact norm_zero.trans_le (norm_nonneg _)
def coversP (p:ι → Support n)(g:ι→ℝ) (i:Clusters ι):= clusters (blocked p) g i.2
def seatP (p:ι→ Support n)(i:Clusters ι): Support n:= unionOf p i.2
def caps (p:ι→Support n)(g:ι→ℝ) (x:Support n):ℝ:= Cap (coversP p g) (seatP p) x
lemma officer (hX: ∀ i,(p i).Nonempty)(h:Trees.Ready p M g a c t u)(hv:∀ i,‖w i‖ ≤g i)(hk:0≤a)(x:Support n): ‖portion p w x‖≤caps p g x:=by
    let f (i:Clusters ι):= if seatP p i=x then termP (blocked p) w i else 0; let g' (i:Clusters ι):= if seatP p i=x then coversP p g i else 0
    have hn:= h.2.2.2.2.1
    have hQ : ∀ i:ι, |g i|=g i:=fun i=>abs_of_nonneg (hn i)
    have hf i: ‖Gas.term (blocked p) g i‖=coversP p g i:=by rw [Gas.term_nonneg]; simp only [Real.norm_eq_abs,hQ,coversP]
    have hm : Summable g':=by
      have hv:= (Gas.absolute (blocked p) g p M (literal_test p hX) hX hk (by simp_rw [Real.norm_eq_abs,hQ]; exact h)).2.1 -- implicit
      simp_rw [hf] at hv; exact somG (k:=coversP p g) ((by simpa only [← hf,norm_norm] using hv) : Summable fun i=> ‖coversP p g i‖) (p:= seatP p) x
    have he' (i): ‖f i‖≤ g' i:=by unfold f g'; split; exact term_bill hv i; exact norm_zero.le
    have hp := hm.of_nonneg_of_le (fun i=> norm_nonneg _) he'
    exact (norm_tsum_le_tsum_norm hp).trans (hp.tsum_le_tsum he' hm)
end YM.QCD.GasP
