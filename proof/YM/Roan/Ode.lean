import YM.Kwick.Victor
import YM.Lapin.Plink
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open Filter Function Set Lattice Wilson RG Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Poised Poised.Beacon Poised.Display Poised.Stative Poised.Sieve
open Finset Tawny Tawny.Cast Tawny.Cast.Rays Tawny.Cast.Carnal Tawny.Cast.TableT Tawny.Pane Tawny.BendR
open Oriole Counting Counting.Click PCAC Patria.Gall.Seals Patria.Gall
-- incomes cost norm.S
local notation "Z"=> RawVec 10
variable {W:Type}[NormedAddCommGroup W][NormedSpace ℂ W]
local notation "R'"=> Flavor 6→ℂ
noncomputable abbrev knotW {W:Type}[NormedAddCommGroup W][NormedSpace ℂ W](p:Flavor 6→ W) (x:R'):W:= ∑ i:Flavor 6, (x i) • p i
variable (Wκ:ℝ)
lemma knots (X:Flavor 6→ W)(v:ℝ)(hX:∀ i:Flavor 6,‖X i‖ ≤ v)(x:R'): ‖knotW X x‖≤6* v*‖x‖:=by
       have hC : ∑ _i:Flavor 6, ‖x‖*v= 6*v*‖x‖:=by simp [Flavor]; ring
       refine (norm_sum_le ..).trans ((Finset.sum_le_sum (s:=univ) (f:=fun i=>‖x i • X i‖) (g:=fun i=>‖x‖* v) fun i _=>?_).trans hC.le)
       rw [norm_smul]; exact mul_le_mul (norm_le_pi_norm _ i) (hX i) (norm_nonneg _) (norm_nonneg _)
lemma knotted (X:Flavor 6 → R')(x:R')(v:ℝ)(hX:∀ i:Flavor 6,‖X i-Pi.single i 1‖ ≤ v): ‖knotW X x - x‖ ≤6*v*‖x‖:=by
       rw [show knotW X x - x=knotW (fun i=> X i - Pi.single i 1) x from ?_]; · exact knots _ _ hX x
       unfold knotW; simp_rw [smul_sub,Finset.sum_sub_distrib]; congr 1; funext i; rw [Finset.sum_apply, Finset.sum_eq_single i]; simp; intro j h hp; simp [Pi.single_eq_of_ne (Ne.symm hp)]; simp
noncomputable def doubleW (F G:Flavor 6→ W) : ((Flavor 6→ℂ)×(Flavor 6→ℂ)) →ₗ[ℂ] W where
       toFun p:= knotW F p.1 + knotW G p.2
       map_add' x y:= by unfold knotW; simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply,add_smul,Finset.sum_add_distrib]; abel
       map_smul' s x:= by change knotW F (s • x.1) + knotW G (s • x.2) =_; unfold knotW; simp only [RingHom.id_apply,Prod.fst_smul,Prod.snd_smul,Pi.smul_apply,smul_eq_mul,mul_smul,smul_add, Finset.smul_sum]
variable (E H₁:Flavor 6 → W)(u v: W→ₗ[ℂ](R'))
noncomputable abbrev Bishop (E HZ:Flavor 6→ W)(u v:W→ₗ[ℂ] (R')):= (u.prod v) ∘ₗ doubleW E HZ
variable (b a:ℝ)
-- hda error budget.L: $6 e ≤min.. order. inverse estimate $12(1+b)$.
structure SplitX (E HZ: Flavor 6→ W)(u v:W→ₗ[ℂ] (Flavor 6→ℂ))(a b:ℝ):Prop where
       pos : 0 ≤ a
       cap : 1 ≤ b
       good: 6*a ≤ 1/4
       tight: (6*a)*(24*b) ≤ 1/4
       plot: ∀ i, ‖u (E i)- Pi.single i 1‖≤ a
       book: ∀ i, ‖v (E i)‖≤ b
       pluck:∀ i, ‖v (HZ i)- Pi.single i 1‖≤ a
       wool : ∀ i, ‖u (HZ i)‖≤ a
variable {E H₁ u v a b} (h:SplitX E H₁ u v a b)
local notation "Tu"=> u ∘ₗ doubleW E H₁
local notation "Tv"=> v ∘ₗ doubleW E H₁
include h
lemma heightsG (p: (R') × (R')) : ‖p‖ ≤ (100*b)*‖Bishop E H₁ u v p‖:=by -- using `W` implicit? binder test.
         let T1:=H₁; rcases p with ⟨x,y⟩; let T:=doubleW E H₁ (x,y); let r:=‖(u T,v T)‖; have hr:0≤r:=norm_nonneg _
         let e:= 6*a; let k:= 6*b; have ht:1≤b:=h.cap; have hz:0 ≤ b:=zero_le_one.trans ht; have he:0 ≤a:=h.pos; have hE:0≤e:=mul_nonneg (by norm_num) he; have hK:0≤k:=mul_nonneg (by norm_num) hz
         let Ex(f:W→ₗ[ℂ] (R')):=knotW (fun i=>f (E i)) x; let Zy(f:W→ₗ[ℂ] (R')):=knotW (fun i=>f (T1 i)) y; have hV(f:W→ₗ[ℂ] (R')): f T=Ex f+Zy f:=by unfold T Ex Zy T1; change f ((∑ _,_)+(∑ _,_))=_; unfold knotW; simp
         have hV' : ‖x‖≤ r + e*(‖x‖+‖y‖):=by
            have hk:‖Ex u - x‖ ≤ e*‖x‖ := knotted _ x a h.plot; have hQ: ‖Zy u‖ ≤e*‖y‖:= knots _ _ h.wool y
            calc ‖x‖=‖u T- (Ex u-x+ Zy u)‖:=by rw [hV]; congr 1; abel
                 _ ≤ _:= (norm_sub_le ..).trans ((add_le_add (show ‖u T‖≤r from le_max_left ..) ((norm_add_le ..).trans ((add_le_add hk hQ).trans_eq (by rw [mul_add])))))
         have hV₂: ‖y‖ ≤ r+ k*‖x‖+e*‖y‖:=by
            have hk:‖Zy v-y‖ ≤ e*‖y‖:= knotted _ y a h.pluck; have hZ:‖ Ex v‖≤ k*‖x‖:= knots _ _ h.book x
            calc ‖y‖= ‖v T-(Ex v+(Zy v-y))‖:=by rw [hV]; congr 1; abel
                 _ ≤ _:= (norm_sub_le ..).trans ((add_le_add (show ‖v T‖≤r from le_max_right ..) ((norm_add_le ..).trans (add_le_add hZ hk))).trans (by linarith))
         have hQ:e*(4*k)≤ 1/4:=by unfold e k; nlinarith only [h.tight]
         have hC:e≤1/4:=h.good
         have hx': ‖y‖≤2*r+2*k*‖x‖:=by linarith only [show e*‖y‖≤1/4*‖y‖ from mul_le_mul_of_nonneg_right hC (norm_nonneg _),hV₂,norm_nonneg y]
         have hz' : ‖x‖ ≤ 4*r:=by
              have h:e*‖x‖ ≤1/4*‖x‖:=mul_le_mul_of_nonneg_right hC (norm_nonneg _); have h':e*‖y‖ ≤1/2*r+(1/8)*‖x‖:=by
                        refine (mul_le_mul_of_nonneg_left hx' hE).trans ?_; nlinarith only [mul_le_mul_of_nonneg_right hQ (norm_nonneg x),mul_le_mul_of_nonneg_right hC hr]
              nlinarith only [hV',h,h',hr]
         change max ‖x‖ ‖y‖ ≤100*b*r; have hp:= mul_le_mul_of_nonneg_right ht hr; unfold k at hx'; apply max_le <;> nlinarith only [norm_nonneg x,norm_nonneg y,hr,hp,hx',hz',mul_le_mul_of_nonneg_left hz' hz] -- product k substitution
lemma facesB : Surjective (Bishop E H₁ u v):=by
       refine LinearMap.surjective_of_injective (LinearMap.ker_eq_bot.mp ?_) -- maybe different lemma.
       refine eq_bot_iff.mpr (fun x hx=>?_); change Bishop E H₁ u v x=0 at hx; have h:= heightsG h x; rw [hx,norm_zero,mul_zero] at h; exact (show x=0 from norm_le_zero_iff.mp h)
lemma voices (x y:R'):∃ p q:R',u (knotW E p+knotW H₁ q)=x∧ v (knotW E p+knotW H₁ q)=y∧‖(p,q)‖ ≤100*b*‖(x,y)‖ :=by
       obtain ⟨⟨p,q⟩,hk⟩:= facesB h (x,y); refine ⟨p,q,congr_arg Prod.fst hk,congr_arg Prod.snd hk,?_ ⟩
       exact (heightsG h (p,q)).trans_eq (congr_arg (fun p=> 100*b*‖p‖) hk)
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.voices
