import YM.Kwick.Arch
/- Two orientations of recurrence. supplied by fee engine. unnormal.B.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open Filter Function Set Lattice Wilson RG Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Poised Poised.Beacon Poised.Display Poised.Stative Poised.Sieve
open Finset Tawny Tawny.Cast Oriole Counting Counting.Click
local notation "Z"=> RawVec 10
variable {d n:ℕ}{a b c j:Axis} (i:Axis)(K:ℕ→Fin 4→Z)(T:Fin 4→ℕ→ℝ)(Y:ℕ→ℝ)(u L Lb G α ε η B0 B E U C m D d₀:ℝ)
local notation "mP" v:arg k:arg=> wages i (K v k)
local notation "X" v:arg=> blip K i v
local notation "τ" x:arg=> (B+2*(L+1)*x)
local notation "M0"=> X n
variable (hL:0≤L)(hα:0 ≤α)(hε:0≤ε)(hT:0 ≤ η)(h:Bowl i K Y T n L α ε)(hm:∀ v,v≤ n → blip K i v ≤ m)(hp:Y n ≤ B)(h0:E≥0)
-- either orientation.Av.Av.B Poll.St.N. Efficiency.Avoid solve strict. linear max via aff scaling. N max globally.Exact.
lemma comparison (x y a b A B :ℝ)(hx:0<x)(hy:x ≤ y)(hA:y ≤ a*y+b)(hb:0 ≤ b)(hB:a*x+b<x): False:=by
      have he:0≤y:=hx.le.trans hy; nlinarith [mul_le_mul_of_nonneg_left hy hb,mul_lt_mul_of_pos_right hB (hx.trans_le hy)] -- third-degree need x*hA
include hL hα hε hT h hp
section south
local notation "Φ" x:arg=> E + ε*(τ x)
local notation "Ω" x:arg=> α*(Φ x)+ ε*(τ x)+η*x
lemma strongX (hk:∀ i,i < n → 2 ≤ T 0 i)(hη:∀ (k:Fin 4),k≠0→∀ i,i<n→ |T k i-1| ≤ η)(ht:wages i (K 0 0) ≤ E)(hμ:0< m)(hh:(Φ m)+3*n*(Ω m)+B< m) :
    (∀ i':ℕ,i'≤ n→ blip K i i'≤ m) ∧ ∀ (v:ℕ)(k:Fin 4), v≤ n→k≠0→ wages i (K v k-K n k) ≤ (n-v:ℕ)*(Ω m):=by
    obtain ⟨x,hx,he⟩:=Finset.exists_max_image (Finset.Iic n) (blip K i) ⟨n,Finset.mem_Iic.mpr le_rfl⟩; have hv:=Finset.mem_Iic.mp hx; let c:= X x; have h':∀ v:ℕ,v≤ n → X v ≤ c:=fun v hu=>he _ (mem_Iic.mpr hu)
    have hs : c ≤ m:=by
          by_contra! hh'; have ht':0 ≤ B:=le_trans (Mp i K T Y L α ε h n le_rfl) hp; have hE:0 ≤ E:=le_trans (wageG i _) ht; have hX:= (highAmt i K T Y L α ε η B E c hL hα hε hT h h' hp hk hη ht x hv).trans (add_le_add_right (add_le_add_right hp _) _)
          change c ≤ _ at hX; let p(v:ℝ):= ((Φ v)+3*n*(Ω v)+B); let b:= p 0; let a:=2*ε*(L+1)+3*n*(α*(2*ε*(L+1))+2*ε*(L+1)+η); have hQ(t): p t=a*t+b:=by unfold p a b p; ring
          have hz:0 ≤ b:=by unfold b p; simp only [mul_zero, add_zero]; positivity
          apply comparison m c a b 0 0 hμ hh'.le _ hz _; rw [← hQ]; exact hX.trans_eq (by unfold p; ring); rwa [←hQ]
    let h: Bowl i K Y T n L α ε:=h; have hb:∀ v:ℕ,v≤ n→ X v≤ m:=fun v hv=>(h' v hv).trans hs
    exact ⟨hb,fun v k hv he=>marches i K T Y L α ε η B E m hL hα hε hT h hb hp hk hη ht k he v hv⟩
end south
section north
-- prices divided: hard component toward reference.H cost mean.Ph
variable (hk:∀ i,i<n →|T 0 i - 1| ≤ η)(hK:∀ (k:Fin 4),k≠0 →∀ i,i<n →|T k i| ≤ 1)
local notation "ϕ" k:arg v:arg=> wages i (K v k-(T k v:ℂ) • K (v+1) k)
local notation "∆" x:arg=> ε*(τ x)+η*x
local notation "Φ" x:arg=> mP n 0 + n*(∆ x)
local notation "Ω" x:arg=> α*(Φ x)+ε*(τ x)
include hm hk
lemma lowStep (v:ℕ)(hv:v<n):wages i (K v 0-K (v+1) 0)≤ ∆ m:=by apply (shift_down i K T 0 v).trans; exact add_le_add (bow0 i K T Y L α ε B m hL hε h hm hp v hv) (mul_le_mul (hk _ hv) ((paso i K (v+1) 0).trans (hm _ hv)) (wageG ..) hT)
lemma lowAmp (v:ℕ)(hv:v≤ n): wages i (K v 0-K n 0)≤ (n-v:ℕ)*(∆ m):=by
     induction hv using Nat.decreasingInduction with
     | self=> rw[sub_self,wageT,Nat.sub_self,Nat.cast_zero,zero_mul]
     | of_succ v hV ih=>rw[show K v 0-K n 0=(K v 0-K (v+1) 0)+(K (v+1) 0-K n 0) from by abel]; exact (wageA ..).trans ((add_le_add (lowStep i K T Y L α ε η B m hL hα hε hT h hm hp hk v hV) ih).trans_eq (by rw [show n-v=n-(v+1)+1 from by omega,Nat.cast_add]; push_cast; ring))
lemma lowCost (v:ℕ)(hv:v≤ n): mP v 0 ≤ Φ m:=by
     have he:0 ≤ m:= le_trans (pass i K v) (hm _ hv); have hz:0 ≤ B:=le_trans (Mp _ _ _ _ _ _ _ h _ le_rfl) hp; let x:= K v 0; let y:= K n 0; suffices hf:wages i x ≤ wages i y+n*(∆ m) by exact hf
     nth_rw 1[show x=y+(x-y) from by abel]; apply (wageA ..).trans; exact add_le_add_right ((lowAmp i K T Y L α ε η B m hL hα hε hT h hm hp hk v hv).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le ..)) (by positivity))) _
include hK
lemma notch (k:Fin 4)(ht:k≠0)(v:ℕ)(hv:v<n): mP v k≤ (mP (v+1) k)+Ω m:=by
     have hg:=h.curve k v hv; rw[if_neg ht] at hg; let a:= T k v; let x:= K v k; let y:=K (v+1) k; change wages i x≤_ ; nth_rw 1[show x=(a:ℂ) • y+(x-(a:ℂ) • y) from by abel]; apply (wageA ..).trans; refine add_le_add ?_ (hg.trans (add_le_add (mul_le_mul_of_nonneg_left (lowCost i K T Y L α ε η B m hL hα hε hT h hm hp hk (v+1) hv) hα) (mul_le_mul_of_nonneg_left (startup i K T Y L α ε B m hL h hm hp (v+1) hv) hε)))
     rw[wageS,Complex.norm_real, Real.norm_eq_abs]; exact mul_le_of_le_one_left (wageG ..) (hK k ht _ hv)
lemma nCost (k:Fin 4)(ht:k≠0)(v:ℕ)(hv:v≤ n): mP v k ≤ mP n k+(n:ℝ)*(Ω m):=by
      suffices H:∀ i:ℕ,i ≤ n→ wages _ (K i k) ≤ wages _ (K n k)+(n-i:ℕ)*(Ω m) by
           have he:0 ≤ m:=le_trans (pass i K _) (hm _ hv); have hz:0 ≤B:=le_trans (Mp _ _ _ _ _ _ _ h _ le_rfl) hp; have hf:0 ≤ Φ m:=le_trans (wageG ..) (lowCost i K T Y L α ε η B m hL hα hε hT h hm hp hk v hv); apply (H v hv).trans; refine add_le_add_right (mul_le_mul_of_nonneg_right ?_ (add_nonneg (mul_nonneg hα hf) (by positivity))) _; exact_mod_cast Nat.sub_le ..
      intro j hJ; induction hJ using Nat.decreasingInduction with
      | self=> rw [Nat.sub_self,Nat.cast_zero,zero_mul,add_zero]
      | of_succ v hV ih=> apply (notch i K T Y L α ε η B m hL hα hε hT h hm hp hk hK k ht v hV).trans; exact (add_le_add_left ih _).trans_eq (by rw [show n-v=n-(v+1)+1 from by omega,Nat.cast_add]; push_cast; ring)
lemma allCost(v:ℕ)(hv:v≤ n) : X v ≤ Φ m + B+ 3*(n*(Ω m)):=by
      have hw:= (h.funds n le_rfl).trans hp; change (∑ i:Fin 4,_:ℝ) ≤_ at hw; unfold blip; rw [Fin.sum_univ_four] at hw ⊢
      have hpZ(k:Fin 4)(ht:k≠0): mP v k ≤ mP n k+n*(Ω m):= nCost i K T Y L α ε η B m hL hα hε hT h hm hp hk hK k ht v hv -- hp from scope
      linarith only [hw,hpZ 1 (by decide),hpZ 2 (by decide),hpZ 3 (by decide),wageG i (K n 0),lowCost i K T Y L α ε η B m hL hα hε hT h hm hp hk v hv]
omit hm
lemma strongY(hμ:0 < m)(hg:(Φ m)+B+3*(n*(Ω m))< m): (∀ v:ℕ,v≤ n→ blip K i v ≤ m) ∧∀ v:ℕ,v ≤ n→ wages i (K v 0-K n 0)≤ (n-v:ℕ)*(∆ m):=by
       obtain ⟨x,hx,hQ⟩:=Finset.exists_max_image (Finset.Iic n) (blip K i) ⟨n,Finset.mem_Iic.mpr le_rfl⟩; have hv:=Finset.mem_Iic.mp hx; let c:= X x; have h':∀ v:ℕ,v≤ n → X v ≤ c:=fun v hu=>hQ _ (mem_Iic.mpr hu)
       have hs: c ≤ m:=by
            by_contra! hx; have ht':0 ≤ B:=le_trans (Mp i K T Y L α ε h n le_rfl) hp; have hX:= allCost i K T Y L α ε η B c hL hα hε hT h h' hp hk hK x hv
            let G(t:ℝ):ℝ:=(Φ t)+B+3*(n*(Ω t)); let a:=2*ε*(L+1); let b:=n*(a+η)+3*n*(α*(n*(a+η))+a); have hG(t):G t=b*t+G 0:=by unfold G b a; ring
            have hz: c ≤ G c:=hX; have ht :0 ≤ G 0:=by unfold G; have ht:= wageG i (K n 0); simp only[mul_zero,add_zero]; positivity
            exact comparison m c b (G 0) 0 0 hμ hx.le (hz.trans_eq (hG c)) ht (lt_of_eq_of_lt (hG m|>.symm) hg)
       have hb:∀ v:ℕ,v≤ n→ X v ≤ m:=fun v hv=>(h' v hv).trans hs
       exact ⟨hb,fun _ hv=> lowAmp i K T Y L α ε η B m hL hα hε hT h hb hp hk _ hv⟩
end north
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.strongX
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.strongY
