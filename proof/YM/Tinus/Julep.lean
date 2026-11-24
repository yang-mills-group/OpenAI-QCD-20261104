import YM.Tinus.Staid
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open YM.QCD UV Function Finset Filter
open scoped BigOperators Topology
-- abstract *two-ended* stable triangular recurrence x normalized lifted p labels. upper from constant S. Wall finite Volume shape, drives higher lanes output physical estimates. inputs positive.Terminal μ and extent bought by aperture.Eta. bounds don't hide n.E
variable {a b c e d q m H ε η r C P D T M :ℝ} (x:ℕ→ Label 8)(s:ℕ→ℝ){n i:ℕ}
set_option quotPrecheck false
local notation "A" i:arg=> laps 6 (x i)
local notation "B" i:arg=> laps 8 (x i)
local notation "J" i:arg=> A i + B i
local notation "Z" m:arg=> T+2*((C+1)* m)
local notation "G" i:arg=>a+ε*(Z i)
local notation "W" m:arg=> D*(G m)+ ε*(Z m)+ η*m
structure Premium (n:ℕ)(C D a T ε η:ℝ): Prop where
    low: 0 ≤ (C:ℝ)
    carry: 0 ≤ D
    birth : laps 6 (x 0) ≤ a
    vote : s n ≤ T
    value(i:ℕ)(hi:i<n): s i ≤ C*(laps 6 (x (i+1))+laps 8 (x (i+1)))+1/2*s (i+1)+(laps 6 (x i)+laps 8 (x i))
    seed : 0 ≤T
    grate: 0 ≤ ε
    grow : 0 ≤ η
    below(i:ℕ)(hi:i<n):2*laps 6 (x (i+1)) ≤ laps 6 (x i) + ε*s (i+1)
    ahead(i:ℕ)(hi:i<n):laps 8 (x i-x (i+1)) ≤ D*laps 6 (x (i+1))+ ε*s (i+1)+ η* laps 8 (x (i+1))
#check Premium
variable (h: Premium x s n C D a T ε η) (hq:∀ i:ℕ,i≤n→(laps 6 (x i)+laps 8 (x i)) ≤ m)
include h hq
lemma respP (hi:i≤n): s i ≤ Z m:=by
      induction hi using Nat.decreasingInduction with
      | self=> have hc := hq n (le_rfl); have hm:0 ≤ m:= (add_nonneg (laps_nn ..) (laps_nn ..)|>.trans hc); have ht:=h.low; exact h.vote.trans (le_add_of_nonneg_right (by positivity))
      | of_succ i hi ih=> exact (h.value i hi).trans ((add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hq _ hi) h.low) (mul_le_mul_of_nonneg_left ih (by norm_num))) (hq i hi.le)).trans (by linarith only [h.seed]))
lemma graft (hi:i ≤ n): A i ≤ G m:=by
      have hp :0 ≤ a:= (laps_nn ..).trans h.birth; have hm:0 ≤ m:= (add_nonneg (laps_nn ..) (laps_nn ..)|>.trans (hq i hi)); have hz:=h.low; have hM: 0 ≤ Z m:=by have hP:=h.seed; positivity ;
      induction i with
      | zero=> exact h.birth.trans (le_add_of_nonneg_right (mul_nonneg h.grate hM))
      | succ i ih => linarith only [hp,h.below i hi,ih (by omega : i ≤ n),mul_le_mul_of_nonneg_left (respP x s h hq hi) h.grate]
lemma adv (hi:i ≤n) : laps 8 (x i-x n) ≤ (n-i:ℕ)*(W m):=by
      induction hi using Nat.decreasingInduction with
      | self=>
          unfold laps; rw [sub_self,Nat.sub_self,Nat.cast_zero,zero_mul]; apply le_of_eq; refine sum_eq_zero fun i _=>?_ ; split; · rw [show (0:Label 8).val=(0:Pol 8) from rfl,map_zero,norm_zero]
          rfl
      | of_succ i hi ih=>
            rw [show n-i=n-(i+1)+1 from (by omega),Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm ((↑(n - (i + 1)):ℝ)*(W m)) (W m)] -- fix picks RHS after.At Label.L
            let p:= (W m); have h0: laps 8 (x i-x (i+1)) ≤ p:= (h.ahead i hi).trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (graft x s h hq hi) h.carry) (mul_le_mul_of_nonneg_left (respP x s h hq hi) h.grate)) (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left (laps_nn ..)).trans (hq _ hi)) h.grow))
            rw [show x i -x n = (x i-x (i+1))+(x (i+1)-x n) from (by abel)]; exact (lap_plus ..).trans (add_le_add h0 ih) -- order
lemma amt (hi:i≤n) : laps 6 (x i)+laps 8 (x i) ≤ G m + ((n:ℝ)*(W m)+ B n):=by
     have hm:0 ≤ m:= (add_nonneg (laps_nn ..) (laps_nn ..)|>.trans (hq i hi)); have ha:0≤a:= (laps_nn ..).trans h.birth; have hc:=h.low; have hd:=h.carry; have he:=h.grate; have hu:=h.grow; have hp:=h.seed; have hh : laps 8 (x i-x n)≤ n*(W m):=(adv x s h hq hi).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le ..)) (by positivity)); refine add_le_add (graft x s h hq hi) ?_
     nth_rw 1 [show x i=(x i-x n)+x n from (by abel)]; exact (lap_plus ..).trans (add_le_add_left hh _)
omit hq
-- affordability config.Full unscaled exponent outputs.G Co.K.M finite.S bounded.D.H.Use.R Time.`requires P>birth.C.M param pick.Calendar beforeL.L for horizon.Actor.Et Price`
set_option maxHeartbeats 630000 in
lemma palate (hM:0<M)(hi : G M+(n*(W M)+ B n)< M) : (∀ i:ℕ,i≤ n→ (laps 6 (x i)+laps 8 (x i))≤ M)∧ laps 8 (x 0-x n) ≤ n*(W M):=by
       let f(i:ℕ):ℝ:=(laps 6 (x i)+laps 8 (x i)); let N:=Iic n; obtain ⟨i,hi',hx⟩:= exists_max_image N f ⟨n,mem_Iic.mpr le_rfl⟩ -- names
       have hp:∀ j≤ n,f j ≤ f i:=fun j h=> hx j (mem_Iic.mpr h); let S:= f i; have hu:= mem_Iic.mp hi'; have hs:= amt x s h hp hu; have hb:= laps_nn (x n) 8; have ha:0 ≤ a:= (laps_nn ..).trans h.birth
       let Q(v:ℝ):= a+ε*(Z v); let Wp(v:ℝ):= (W v); let a':= h.low
       have hφ:S ≤ M:= by
          by_contra! hr; let q:= S/M; have hV: 1 < q:=(one_lt_div hM).mpr hr; have hq:0<q:= lt_trans zero_lt_one hV; have hX: S=q*M:=(div_mul_cancel₀ S hM.ne').symm
          have hc: Z S ≤ q*(Z M):=by rw [hX,mul_add]; exact add_le_add (le_mul_of_one_le_left h.seed hV.le) (le_of_eq (by ring)) -- rw hX self q loop.Near
          have h':Q S≤ q*Q M:=(add_le_add (le_mul_of_one_le_left ha hV.le) (mul_le_mul_of_nonneg_left hc h.grate)).trans_eq (by unfold Q; ring)
          have hw:Wp S≤ q*Wp M:=(add_le_add (add_le_add (mul_le_mul_of_nonneg_left h' h.carry) (mul_le_mul_of_nonneg_left hc h.grate)) (le_of_eq (congr_arg (η * ·) hX))).trans_eq (by unfold Wp Q; ring)
          have hV' := add_le_add h' (add_le_add (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg n)) (le_mul_of_one_le_left hb hV.le))
          refine (not_lt_of_ge (le_refl S)) ?_ -- rewrite later
          calc S ≤ Q S+(n*Wp S+B n):= hs
               _ ≤ q*Q M + (n*(q*Wp M)+q*(B n)):=hV'
               _= q*(Q M+(n*(W M)+B n)):=by unfold Wp Q; ring
               _ < q*M := mul_lt_mul_of_pos_left hi hq
               _= S:= hX.symm
       have h' :∀ j,j≤ n→(laps 6 (x j)+laps 8 (x j)) ≤ M:= fun j h=> (hp j h).trans hφ; refine ⟨h',?_⟩; exact (by simpa only [Nat.sub_zero] using adv x s h h' (Nat.zero_le n)) -- flag
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.palate
