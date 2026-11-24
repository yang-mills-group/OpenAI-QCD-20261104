import YM.Play.Bois
/-! # lifts (linear). unnormalised row charge on Directions.
 local to these alphabets. Include marker wings in norm. No positivity condition.
 provides perturbation tensor bound without sum over input sites -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Anomaly
open Function MeasureTheory Filter Finset NormedSpace Creek Ledge Grass Matrix
open scoped BigOperators Topology ContDiff Classical Matrix
variable {A B T: Type*}[Fintype A][Fintype B]{X U V:Finset A}{Z :Finset B}{n m i k:ℕ}{C D K s t:ℝ}
variable (M N: Matrix A B ℂ)
def bills (U:Finset A)(s:ℝ):Prop:=∀ i∈U,∑ j,‖M i j‖≤s
lemma sendsAtom {i}(hi:i∈U)(hp:bills M U s): ‖changeVars M (atom i)‖ ≤ s:=by rw [change_atom]; exact (norm_sum_le ..).trans (by simpa only [norm_smul,norm_atom,mul_one] using hp _ hi)
lemma sendsGap {i}(hi:i∈U)(hp:bills (M-N) U s): ‖changeVars M (atom i)-changeVars N (atom i)‖≤s:=by rw [show changeVars M (atom i)-changeVars N (atom i)=changeVars (M-N) (atom i) from ?_]; exact sendsAtom _ hi hp; rw [change_atom,change_atom,change_atom,← sum_sub_distrib]; exact sum_congr rfl fun j _=>(sub_smul ..).symm
lemma volts (L:List A)(h:∀ i∈L,i∈U)(hp:bills M U s) (hs:0 ≤ s): ‖changeVars M (L.map atom).prod‖ ≤ s^L.length:=by
    induction L with
    | nil=> simp
    | cons i L ih=> rw [List.map_cons,List.prod_cons,List.length_cons,pow_succ',map_mul]; exact (norm_mul_le ..).trans (mul_le_mul (sendsAtom M (h _ (List.mem_cons_self ..)) hp) (ih fun i hi=>h i (List.mem_cons_of_mem _ hi)) (norm_nonneg _) hs)
lemma bonk (L:List A)(h:∀ i∈L,i∈U)(hp:bills M U s)(hx:bills N U s)(he:bills (M-N) U t) (hs:1 ≤ s)(ht:0 ≤t): ‖changeVars M (L.map atom).prod-changeVars N (L.map atom).prod‖ ≤ (L.length:ℝ)*t*s^L.length:=by
    induction L with
    | nil=> simp
    | cons i L ih=>
      have hi:=h i (List.mem_cons_self ..); have hL i (hi:i∈L):i∈U:= h _ (List.mem_cons_of_mem _ hi); have hs':0 ≤s:=zero_le_one.trans hs; let a:=changeVars M (atom i); let b:=changeVars N (atom i); let x:=changeVars M (L.map atom).prod; let y:=changeVars N (L.map atom).prod
      have h1:‖a*x-b*x‖≤t*s^L.length:=by rw [← sub_mul]; exact (norm_mul_le ..).trans (mul_le_mul (sendsGap M N hi he) (volts M L hL hp hs') (norm_nonneg _) ht)
      have h₂:‖b*x-b*y‖≤s*(L.length*t*s^L.length):=by rw [← mul_sub]; exact (norm_mul_le ..).trans (mul_le_mul (sendsAtom N hi hx) (ih hL) (norm_nonneg _) hs')
      rw [List.map_cons,List.prod_cons,map_mul,map_mul,List.length_cons,pow_succ']; push_cast; refine (norm_sub_le_norm_sub_add_norm_sub (a*x) (b*x) (b*y)).trans ((add_le_add h1 h₂).trans ?_)
      have h0:= le_mul_of_one_le_right (show 0 ≤ t*s^L.length from by positivity) hs; linarith only [h0]
private lemma rateBasis {S: Alg A→ₗ[ℂ]Alg B}(h:∀ i⊆U,i.card≤n→ ‖S (mono i)‖ ≤ C)(hc:0 ≤ C){x:Alg A}(hx:x∈ Rim U n): ‖S x‖ ≤ C*‖x‖:=by
    conv_lhs=>rw [Rim.record hx,map_sum]
    rw [Grass.norm_def x,Finset.mul_sum]; refine (norm_sum_le ..).trans ((sum_le_sum ?_).trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (?_))); intro i hi; rw [map_smul,norm_smul,mul_comm]; obtain ⟨hz,hg⟩:=mem_filter.mp hi; exact mul_le_mul_of_nonneg_right (h _ (mem_powerset.mp hz) hg) (norm_nonneg _)
    exact fun _ _ _=> mul_nonneg hc (norm_nonneg _)
lemma sendsTotal {x:Alg A}(hx:x∈ Rim U n)(h:bills M U s)(hs:1 ≤ s): ‖changeVars M x‖ ≤s^n*‖x‖:=by
    have hz:0 ≤ s:=zero_le_one.trans hs; refine rateBasis (S:=(changeVars M).toLinearMap) (?_) (by positivity) hx
    intro i hp ht; obtain ⟨f,hf,hf',r⟩:=expression i; have hh j(hj:j∈List.ofFn f): j ∈ U :=hp ((hf' j).2 (by simpa using hj))
    rw [r]; change ‖changeVars M _‖ ≤ _
    exact le_trans (b:=s^i.card) (by simpa only [List.map_ofFn,List.length_ofFn] using volts M _ hh h hz) (pow_le_pow_right₀ hs ht)
lemma sendsDiff {x:Alg A}(hx:x∈ Rim U n)(h:bills M U s)(hp:bills N U s)(hs:1 ≤ s)(he:bills (M-N) U t)(ht:0 ≤ t) : ‖changeVars M x-changeVars N x‖ ≤ n*t*s^n*‖x‖:=by
    have hz:0 ≤ s:=zero_le_one.trans hs; refine rateBasis (S:=(changeVars M).toLinearMap-(changeVars N).toLinearMap) (?_) (by positivity) hx
    intro i hi hv; obtain ⟨f,hf,hf',r⟩:= expression i; have hh j (hj:j∈List.ofFn f): j∈U:=hi ((hf' j).2 (by simpa using hj))
    rw [r]; change ‖changeVars M _-changeVars N _‖ ≤ _; have h:‖changeVars M _- changeVars N _‖ ≤ i.card*t*s^i.card:= (by simpa only [List.map_ofFn,List.length_ofFn] using bonk M N _ hh h hp he hs ht) -- metas fill
    exact h.trans (by gcongr)
-- Patio Full Wick law
open Cove
def branch (W:Matrix A A ℂ) : Patio A→ₗ[ℂ] Patio A:= ((birth (Wand W)).toLinearMap.comp (light A).toLinearMap).codRestrict (roomA A).toSubmodule fun x=> (stout W).birthP.evenPay (bright x)
def mobilize (W:Matrix A B ℂ): Patio A→ₐ[ℂ] Patio B:= car (changeVars W) (fun x h=> (exterior_parity _ x).trans (congr_arg _ h))
def splash (W :Matrix A A ℂ): Patio A→ₗ[ℂ] Patio B:= (mobilize M).toLinearMap.comp (branch W)
lemma splashMem (W:Matrix A A ℂ)(h:∀ i∈U,∀ j,M i j ≠0 → j∈ Z){x:Patio A}(hx:x.val∈ Rim U k): (splash M W x).val ∈ Rim Z k:= Rim.patched M h (meadow W hx)
lemma splashSum (W:Matrix A A ℂ)(hp:bills M U s)(hs:1 ≤s)(h:∀ i∈U,∀ j∈U,‖W i j‖ ≤C)(hc:0 ≤ C) {x:Patio A}(hh:x.val∈Rim U n): ‖splash M W x‖≤ s^n*dime n C*‖x‖:= by rw [mul_assoc]; exact (sendsTotal M (meadow W hh) hp hs).trans (mul_le_mul_of_nonneg_left (coupon W h hc hh) (pow_nonneg (zero_le_one.trans hs) _))
def shiver (n:ℕ)(s C v w :ℝ):ℝ:= s^n * (n*v*dime n C+percent n C*w)
lemma splashDiff (P Q: Matrix A A ℂ)(hp:bills M U s)(hx:bills N U s)(hs:1 ≤ s)(hN:bills (M-N) U D)(hd:0≤ D) (h:∀ i∈U,∀ j∈U,‖P i j‖≤ C)(he:∀ i∈U,∀ j∈U, ‖Q i j‖ ≤C)(h':∀ i∈U,∀ j∈U,‖P i j-Q i j‖≤ t)(ht:0 ≤ t)(hC:0 ≤ C){x:Patio A}(hb:x.val∈Rim U n):
    ‖splash M P x - splash N Q x‖ ≤ shiver n s C D t* ‖x‖:=by
    let y:= birth (Wand P) x.val; let z:= birth (Wand Q) x.val; have hy:y ∈ Rim U n:= meadow P hb; have hz : z∈ Rim U n:= meadow Q hb
    have hh:‖changeVars N y-changeVars N z‖≤ s^n * (percent n C * t *‖x‖):=by rw [← map_sub]; exact (sendsTotal N (Submodule.sub_mem _ hy hz) hx hs).trans (mul_le_mul_of_nonneg_left (interest P Q h he h' ht hC hb) (pow_nonneg (zero_le_one.trans hs) _))
    have hf:= (sendsDiff M N hy hp hx hs hN hd).trans (mul_le_mul_of_nonneg_left (coupon P h hC hb) (show 0 ≤ n*D*s^n from mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hd) (pow_nonneg (zero_le_one.trans hs) _)))
    refine (norm_sub_le_norm_sub_add_norm_sub (changeVars M y) (changeVars N y) (changeVars N z)).trans ((add_le_add hf hh).trans ?_)
    unfold shiver; rw [show ‖x‖=‖x.val‖ from rfl]; exact (le_of_eq (by ring))
lemma ponds (P:Matrix A A ℂ) : branch P 1=1:=Subtype.ext (powers _ _ (vacant _ (A:=A) (U:=Finset.univ) (Rim.one _)))
end YM.QCD.Anomaly
#print axioms YM.QCD.Anomaly.splashDiff
