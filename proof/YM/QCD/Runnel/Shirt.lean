import YM.QCD.Runnel.Hover

/-! # bi-packs and sharp structured approximants -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Run
open Lat Lattice Wilson Cost Function Finset Kit
open scoped Matrix Matrix.Norms.L2Operator BigOperators
variable {f : Side} {I : Type*} {δ b c R R' S S' : ℝ} {B v p n m : ℕ}
abbrev St (f : Side):= Grid f→Sheet f
variable {M N X Y : St f}

def Pride (δ b : ℝ) (B : ℕ) (M : St f) (p : ℝ) := Own f δ b B M p ∧ Own f δ b B (star M) p
lemma Pride.mono (h : Pride δ b B M R) (ht : R≤S): Pride δ b B M S:=⟨h.1.mono ht,h.2.mono ht⟩
lemma Pride.void : Pride δ b B (0:St f) 0:= ⟨Heritage.vacant,by rw [star_zero]; exact Heritage.vacant⟩ -- check
lemma Pride.ad (h : Pride δ b B M R): Pride δ b B (star M) R:=⟨h.2,by rw [star_star]; exact h.1⟩
lemma Pride.plus (h : Pride δ b B M R) (e : Pride δ b B N S): Pride δ b B (M+N) (R+S):=⟨h.1.plus e.1,by rw [star_add]; exact h.2.plus e.2⟩
lemma Pride.scale (t : ℂ) (h : Pride δ b B M R): Pride δ b B (t • M) (‖t‖*R):= ⟨h.1.scalar .., by rw [star_smul]; simpa only [norm_star] using h.2.scalar (star t)⟩ -- star s?
lemma Pride.minus (h : Pride δ b B M R) (e : Pride δ b B N S): Pride δ b B (M-N) (R+S):= ⟨h.1.sub e.1, by rw [star_sub]; exact h.2.sub e.2⟩
lemma Pride.prod (h : Pride δ b B M R) (e : Pride δ b B N S) (hd : 0<δ) (hp : 0≤b) (hr : 0≤R) (hs : 0≤S): Pride δ b B (M*N) (R*S):= ⟨h.1.meet e.1 hd hp hr hs,by rw [star_mul,mul_comm R S]; exact e.2.meet h.2 hd hp hs hr⟩
lemma Pride.group (T : Finset I) {X : I→St f} {R : I→ℝ} (h : ∀ i∈T, Pride δ b B (X i) (R i)): Pride δ b B (∑ i∈T,X i) (∑ i∈T,R i):=by
  classical
  induction T using Finset.induction_on with
  | empty => rw [sum_empty,sum_empty]; exact void
  | insert i t ht ih=>rw [sum_insert ht,sum_insert ht]; exact (h _ (mem_insert_self ..)).plus (ih (fun i hi=> h _ (mem_insert_of_mem hi)))
lemma Pride.hotel {X : I→St f} {R : I→ℝ} (hd : 0<δ) (hp : 0≤b) (hm : Summable R) (h : ∀ i, Pride δ b B (X i) (R i)) (he : ∀ U, HasSum (fun i=> X i U) (M U)): Pride δ b B M (∑' i,R i):= ⟨Heritage.congregation hd hp (fun i=>(h i).1) hm he, Heritage.congregation hd hp (fun i=>(h i).2) hm (fun U=> (he U).star)⟩
lemma Pride.stiff (hb : 0≤b): Pride δ b B (1:St f) (Real.exp b):=⟨Heritage.heritage_one _ hb,by rw [star_one]; exact Heritage.heritage_one _ hb⟩
lemma Pride.trail (t : Site f) (w : Walk) (hb : 0≤b) (hd : 0<δ) (hc : 0<c) (hr : 0<n) (ht : 2*n≤B) (hg : Pile b (2*n)*gal δ^n≤ Real.exp (c*n)): Pride δ b B (fun U=>routeM t U w) (Real.exp (c*n)*Real.exp (c*w.length)):= by
  refine ⟨rides_for t w hb hd hc hr ht hg,?_⟩
  rw [show star (fun U : Grid f=> routeM t U w)=(fun U=>routeM t U (Lattice.reverse w)) from funext fun i=> (flipping ..).symm]
  simpa only [Lattice.reverse,List.length_map,List.length_reverse] using rides_for t (Lattice.reverse w) hb hd hc hr ht hg

lemma Reads.count (T : Finset I) {X : I→St f} (h : ∀ i∈T, Reads eye eye m (X i)): Reads eye eye m (∑ i∈T,X i):=by
  classical
  induction T using Finset.induction_on with
  | empty=> rw [sum_empty]; exact Reads.empty
  | insert i t ht ih=> rw [sum_insert ht]; exact (h _ (mem_insert_self ..)).plus (ih (fun i hi=>h _ (mem_insert_of_mem hi)))

-- bound of approximant edges specified separately to enable arithmetic
structure Sample (δ b c : ℝ) (B : ℕ) (M X : St f) (R : ℝ) (p v : ℕ): Prop where
 pay : 0≤ R
 all : Pride δ b B M R
 keeps : Pride δ b B X R
 close : Pride δ b B (M-X) (R*Real.exp (-c*p))
 size : Reads eye eye v X
namespace Sample
lemma mono (h : Sample δ b c B M X R p v) (hr : R≤S) (ht : v≤n): Sample δ b c B M X S p n:= ⟨h.pay.trans hr,h.all.mono hr,h.keeps.mono hr,h.close.mono (mul_le_mul_of_nonneg_right hr (by positivity)),h.size.dilate ht⟩
lemma zero : Sample δ b c B (0:St f) 0 0 p v:= by refine ⟨le_rfl,Pride.void,Pride.void,?_,Reads.empty⟩; simpa using Pride.void (δ:=δ) (b:=b) (B:=B) (f:=f)
lemma exact_X (h : Pride δ b B M R) (he : Reads eye eye v M) (hr : 0≤R): Sample δ b c B M M R p v:=by refine ⟨hr,h,h,?_,he⟩; rw [sub_self]; exact Pride.void.mono (by positivity)
lemma one (hb : 0≤b): Sample δ b c B (1:St f) 1 (Real.exp b) p v:= exact_X (Pride.stiff hb) Reads.single (by positivity)
lemma both (h : Sample δ b c B M X R p v) (e : Sample δ b c B N Y S p v): Sample δ b c B (M+N) (X+Y) (R+S) p v:=by
  refine ⟨add_nonneg h.pay e.pay,h.all.plus e.all,h.keeps.plus e.keeps, ?_,h.size.plus e.size⟩; rw [add_mul, show M+N-(X+Y)=M-X+(N-Y) by abel]; exact h.close.plus e.close
lemma scalar (h : Sample δ b c B M X R p v) (t : ℂ): Sample δ b c B (t • M) (t • X) (‖t‖*R) p v:=by refine ⟨mul_nonneg (norm_nonneg _) h.pay,h.all.scale t,h.keeps.scale t,?_,h.size.coin t⟩; rw [← smul_sub,mul_assoc]; exact h.close.scale t
lemma apart (h : Sample δ b c B M X R p v) (e : Sample δ b c B N Y S p v): Sample δ b c B (M-N) (X-Y) (R+S) p v:=by rw [sub_eq_add_neg,sub_eq_add_neg]; exact h.both (by simpa only [neg_one_smul,norm_neg,norm_one,one_mul] using e.scalar (-1))
lemma bond (h : Sample δ b c B M X R p v) (e : Sample δ b c B N Y S p n) (hd : 0<δ) (hp : 0≤b): Sample δ b c B (M*N) (X*Y) (R*S+R*S) p (v+n):=by
  have he:=h.pay; have ht:= e.pay; have hpr : R*S≤R*S+R*S:=le_add_of_nonneg_right (by positivity)
  refine ⟨by positivity,(h.all.prod e.all hd hp he ht).mono hpr,(h.keeps.prod e.keeps hd hp he ht).mono hpr, ?_, h.size.across e.size⟩
  rw [show M*N-X*Y=(M-X)*N+X*(N-Y) by noncomm_ring,add_mul,mul_right_comm R S (Real.exp _),show R*_ *S+_= R*Real.exp (-c*p)*S+ R*(S*Real.exp (-c*p)) by ring]; exact (h.close.prod e.all hd hp (by positivity) ht).plus (h.keeps.prod e.close hd hp he (by positivity))
lemma adj (h : Sample δ b c B M X R p v): Sample δ b c B (star M) (star X) R p (v+v):= ⟨h.pay,h.all.ad,h.keeps.ad,by rw [← star_sub]; exact h.close.ad,h.size.turn⟩
lemma group (T : Finset I) {W Z : I→St f} {R : I→ℝ} (h : ∀ i∈T, Sample δ b c B (W i) (Z i) (R i) p v): Sample δ b c B (∑ i∈T,W i) (∑ i∈T,Z i) (∑ i∈T,R i) p v:=by
  classical
  induction T using Finset.induction_on with
  | empty=>rw [sum_empty,sum_empty,sum_empty]; exact zero
  | insert i t ht ih=> rw [sum_insert ht,sum_insert ht,sum_insert ht]; exact (h i (mem_insert_self ..)).both (ih fun i hi=> h _ (mem_insert_of_mem hi))
end Sample
end YM.QCD.Run
