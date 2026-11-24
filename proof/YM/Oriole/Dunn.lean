import YM.Tinus.Pace
import YM.Oriole.Hoop
/-! Fray gas budgeting. True Premium startup inequality with s0, never conditioned on price due Vol. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open Function Finset Filter UV Lattice Wilson
open scoped BigOperators ContDiff Topology Classical
variable {a b c e d q m H ε η r C P D T M :ℝ} (x:ℕ→ Label 8)(s:ℕ→ℝ){n i:ℕ}
set_option quotPrecheck false
local notation "A" i:arg=> laps 6 (x i)
local notation "B" i:arg=> laps 8 (x i)
local notation "J" i:arg=> A i + B i
local notation "Z" m:arg=> T+2*((C+1)* m)
local notation "u" x:arg=> a+ d*x
local notation "G" i:arg=> u (Z i)+ε*(Z i)
local notation "W" m:arg=> D*(G m)+ ε*(Z m)+ η*m
variable (h0:Premium x s n C D (a+d*s 0) T ε η)(hd:0 ≤ d)(ha:0 ≤ a)
include h0 hd
lemma fortune(h: s 0 ≤ P):Premium x s n C D (a+d*P) T ε η:={h0 with birth:=h0.birth.trans (add_le_add_right (mul_le_mul_of_nonneg_left h hd) _)} -- Lean add_left
include ha
lemma vernal(hM:0<M)(hi:G M+(n*(W M)+ B n)< M): (∀ i≤n,laps 6 (x i)+laps 8 (x i) ≤ M) ∧ laps 8 (x 0-x n) ≤ n*(W M)∧ s 0 ≤ Z M :=by
       let f(i:ℕ):ℝ:=(laps 6 (x i)+laps 8 (x i)); let N:=Iic n; obtain ⟨i,hi',hx⟩:= exists_max_image N f ⟨n,mem_Iic.mpr le_rfl⟩
       have hp:∀ j≤ n,f j ≤ f i:=fun j h=> hx j (mem_Iic.mpr h); let S:= f i; have hu:= mem_Iic.mp hi'; have hrZ:= respP x s h0 hp (Nat.zero_le _); have hσ:= fortune x s h0 hd hrZ; have hs:= amt x s hσ hp hu; have hb:= laps_nn (x n) 8
       let Q(v:ℝ):= (G v); let Wp(v:ℝ):= (W v)
       have hφ:S ≤ M:= by
          by_contra! hr; let q:= S/M; have hV: 1 < q:=(one_lt_div hM).mpr hr; have hq:0<q:= lt_trans zero_lt_one hV; have hX: S=q*M:=(div_mul_cancel₀ S hM.ne').symm
          have hc: Z S ≤ q*(Z M):=by rw [hX,mul_add]; exact add_le_add (le_mul_of_one_le_left hσ.seed hV.le) (le_of_eq (by ring))
          have h':Q S≤ q*Q M:=(add_le_add (add_le_add (le_mul_of_one_le_left ha hV.le) (mul_le_mul_of_nonneg_left hc hd)) (mul_le_mul_of_nonneg_left hc hσ.grate)).trans_eq (by unfold Q; ring)
          have hw:Wp S≤ q*Wp M:=(add_le_add (add_le_add (mul_le_mul_of_nonneg_left h' hσ.carry) (mul_le_mul_of_nonneg_left hc hσ.grate)) (le_of_eq (congr_arg (η * ·) hX))).trans_eq (by unfold Wp Q; ring)
          have hV' := add_le_add h' (add_le_add (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg n)) (le_mul_of_one_le_left hb hV.le))
          refine (not_lt_of_ge (le_refl S)) ?_
          calc S ≤ Q S+(n*Wp S+B n):= hs
               _ ≤ q*Q M + (n*(q*Wp M)+q*(B n)):=hV'
               _= q*(Q M+(n*(W M)+B n)):=by unfold Wp Q; ring
               _ < q*M := mul_lt_mul_of_pos_left hi hq
               _= S:= hX.symm
       have h':∀ j:ℕ,j≤ n→(laps 6 (x j)+laps 8 (x j)) ≤ M:= fun j h=> (hp j h).trans hφ; have he:= respP x s h0 h' (Nat.zero_le _); have hv:= fortune x s h0 hd he; exact ⟨h',(by simpa only [Nat.sub_zero] using adv x s hv h' (Nat.zero_le n)),he⟩
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.vernal
namespace YM.Massive.Oriole
open Poised.Plans UV Poised Poised.Beacon QCD QCD.Lat QCD.Grass Poised.Plans.Stamp.Stair Poised.Stative Function Finset Filter Lattice Wilson Poised.Display
open scoped BigOperators ContDiff Topology Classical TensorProduct
variable {d:ℕ} (p q:Flavor 6)(g: Bool)(z w t a b:ℂ)
local notation "F"=> flame p q g 8 (by decide)
local notation "G" i:arg=> arbor p q g i
local notation "Y"=> z • F+w • arbor p q g true + t • arbor p q g false
private lemma tribunes (k:ℕ)(B:Label d): laps k (z • B)= ‖z‖ * laps k B:=by
      unfold laps; rw[mul_sum]; refine sum_congr rfl fun j _=>?_ ; split ; next h=> change ‖coord _ (z • B.val)‖=_; rw[map_smul,norm_smul]
      next _=> rw[mul_zero]
lemma outside (t:Bool) : geometry 8 (arbor p q g t).val=(arbor p q g t).val:=by
      rw [arbola p q g t,map_sum]; apply sum_congr rfl; intro i _; let u:=one_jet t i; let v:=one_jet (!t) i
      rw [← j_stard]; change geometry 8 (jcoat (fieldB p q u v _))= _; unfold fieldB; simp_rw [map_sum]; refine sum_congr rfl fun x _=> sum_congr rfl fun y _=>?_ ; let m: SpinMode 8:=((u,x),p); let n: SpinMode 8:=((v,y),q); let z:ℂ:=wave (claw g i) x y
      have hP:geometry 8 (jcoat (Matrix.single m n 1))=jcoat (Matrix.single m n 1):=by
           obtain ⟨h,hP⟩:=soldF m n; rcases hP with hP|hP
           · rw [←hP,geometry_basis,if_pos (h.trans (jet_value i t))]
           apply neg_injective; rw [← map_neg, ← hP, geometry_basis,if_pos (h.trans (jet_value i t))]
      change geometry 8 (jcoat (Matrix.single m n z))=_; rw [show Matrix.single m n z=z • Matrix.single m n (1:ℂ) from by ext i j; rw [Matrix.single_apply, Matrix.smul_apply,Matrix.single_apply]; split <;> simp,map_smul,map_smul,hP] -- rhs p q leg uses let causing rw?
lemma podium : laps 6 (Y)=‖z‖*laps 6 F:=by
     rw [← tribunes]; unfold laps; apply sum_congr rfl; intro i _; split
     next h =>
        have hp(t:Bool): Poised.Stative.coord i.val (G t).val=0:=by rw[← outside p q g t, geo_basis,if_neg (h ▸ (by decide))]
        change ‖ Poised.Stative.coord _ (z • (F).val+w • (G true).val+ t • (G false).val)‖= _; rw [map_add,map_add,map_smul (Poised.Stative.coord i.val) w,map_smul (Poised.Stative.coord i.val) t, hp,hp,smul_zero,smul_zero,add_zero,add_zero]; rfl
     next _=> rfl
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.podium
