import YM.Roan.Regal
import YM.Rill.Comes
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
set_option maxHeartbeats 750000
namespace YM.Massive.Tarn.ChargeQ
open Function Set Filter
open Lattice Wilson QCD QCD.Lat
open UV Patria Patria.Depth Patria.Hub Poised Poised.Plans Poised.Plans.Stamp
open Choir Choir.Strip Quilt Massive.Patria.Gall Massive.Patria.Gall.Onyx
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix.Norms.Frobenius InnerProductSpace
variable {C:Sequence}{P:Calibration C}{K:Choir}{φ:ℕ→ℕ}{β e:ℝ}(hp:C.Path β e)(hP:P.System)(hφ:Tendsto φ atTop atTop)
variable (F:Pollens P K)(hf:Foil P K F)(HQ:K.Harmony P φ)
variable (x y:E4)(a b:Axis)
local notation "S"=> K.total
include hp hP hφ HQ F
open Finset
variable (v w: K.W)
local notation "T"=> (0:Fin 2)
local notation "x'"=> points ![x,y]
open Matrix
lemma neighbor (he:x≠y): (points ![x,y])∈conf 2:=by intro i j; fin_cases i<;>fin_cases j<;> first| simp [*,Ne.symm he] -- fix
local notation "X" t:arg=> x+t • basis a
lemma trailX (t:ℝ): points ![X t,y]=points ![x,y]+ t • Points.direction T a:=by apply PiLp.ext; intro i; fin_cases i<;>simp [Points.direction]
lemma traiY (t:ℝ): points ![x,y+t • basis a]=points ![x,y]+ t • Points.direction (1:Fin 2) a:=by apply PiLp.ext; intro i; fin_cases i<;>simp [Points.direction]
local instance choirX (n:ℕ):ContinuousSMul ℝ (Points n):= inferInstance
lemma shore : HasDerivAt (fun t:ℝ=>points ![X t,y]) (Points.direction T a) 0:=by rw [funext (fun t:ℝ=> trailX hp hP hφ F HQ x y a t)]; simpa only [one_smul] using! (((hasDerivAt_id' (0:ℝ)).smul_const (Points.direction (n:=2) T a)).const_add (points ![x,y]))
lemma path_y :HasDerivAt (fun t:ℝ=>points ![x,y+t • basis a]) (Points.direction (1:Fin 2) a) 0:=by rw [funext (fun t:ℝ=> traiY hp hP hφ F HQ x y a t)]; simpa only[one_smul] using! (((hasDerivAt_id' (0:ℝ)).smul_const (Points.direction (1:Fin 2) a)).const_add (points ![x,y]))
omit hp hP hφ F
include HQ
lemma ear_t(x:Points 2)(hp:x∈conf 2)(V:ℝ→ Points 2)(j:Fin 2)(t:ℝ)(hV: V 0=x)(he: HasDerivAt V (t • Points.direction j a) 0): HasDerivAt (fun y=> S 2 (V y) (![v,w])) (t • S 2 x (update (![v,w]) j (K.arc a ((![v,w]) j)))) 0:=by
         subst x; have hx := ((HQ.h.smooth 2 (![v,w])).differentiableOn (by simp)).differentiableAt ((conf_open _).mem_nhds hp)
         have hk:=hx.hasFDerivAt.comp_hasDerivAt 0 he; rw [map_smul,show fderiv ℝ _ _ (Points.direction (n:=2) j a)=_ from HQ.h.derivatives _ _ hp _ _ _] at hk; exact hk
-- first/second exact.
omit HQ -- accidental included above earlier.N
lemma update0(x y z:K.W): update (![x,y]) (0:Fin 2) z= ![z,y]:=by funext i; fin_cases i<;>simp
lemma update1(x y z:K.W): update (![x,y]) (1:Fin 2) z= ![x,z]:=by funext i; fin_cases i<;>simp
local notation "tQ"=> (Signed.reflect b)
local notation "J"=> F.adj b
local notation "N" p:arg=>Ortho.move (Signed.reflect b) p
local notation "sg"=> signT (Signed.mirror b) a
include hp hP hφ F HQ
lemma adj_actsT (t:ℝ)(he: points ![X t,y]∈ conf 2): S 2 (points ![N y, N (X t)]) ![J w,J v]=star (S 2 (points ![X t,y]) ![v,w]):=by
         have h:= HarmonyF.swung hp HQ hφ hP F (points ![X t,y]) he (![v,w]) b -- args
         convert h using 2
         · apply congrArg (K.total 2); apply PiLp.ext; intro i; fin_cases i <;> rfl
         funext i; fin_cases i<;>rfl
omit hp hP hφ F HQ
lemma norm_b: N (basis a)= sg • (basis a):=by by_cases he:b=a<;> (ext i; rw[Signed.mirrored]; by_cases h:i=b<;>by_cases ht:i=a<;>first|simp [he,signT,Signed.mirror,h,ht]; try simp_all)
include hp hP hφ F HQ
lemma reversal(hx:x≠ y): S 2 (points ![N y,N x]) ![J w,(sg:ℂ) • K.arc a (J v)] = star (S 2 (points ![x,y]) ![K.arc a v,w]):=by
       let d(t:ℝ):=points ![X t,y]; let z(t:ℝ):= points ![N y,N (X t)]; let Xp:= x'; let Zh:= z 0; have ht:d 0=x':=by unfold d; simp
       have hz:Zh=points ![N y,N x]:=by unfold Zh z; simp
       have h₂: z=(fun t=>points ![N y,N x+(sg*t) • basis a]):=by funext t; unfold z; rw [show N (X t)= N x + t • (N (basis a)) from (map_add (Ortho.motion tQ) x _).trans (congr_arg (N x + ·) (map_smul (Ortho.motion tQ) t _)),norm_b,smul_smul, mul_comm]
       have hv : x'∈ conf 2:= neighbor hp hP hφ F HQ x y hx -- included
       have he:HasDerivAt d (Points.direction T a) 0:=shore hp hP hφ F HQ x y a
       have hX : N y≠ N x:=(Ortho.motion tQ).injective.ne (Ne.symm hx)
       have hh:S 2 (points ![N y,N x]) ![J w,(↑sg:ℂ) • K.arc a (J v)] = sg • (S 2 (points ![N y,N x]) ![J w,K.arc a (J v)]):=by
             rw [← update1 (J w) (J v), (S _ _).map_update_smul,update1]; rfl -- ℝ vs ℂ
       have hg:HasDerivAt z (sg • Points.direction (1:Fin 2) a) 0:=by
             rw[h₂]; have ht':HasDerivAt (fun t:ℝ=> sg*t) sg 0:=by simpa only[mul_one] using ((hasDerivAt_id' (0:ℝ)).const_mul sg);
             rw [funext fun i=> traiY hp hP hφ F HQ (N y) (N x) a (sg*i)]; exact ((ht'.smul_const _).const_add _)
       let p₁ (t:ℝ):=S 2 (z t) ![J w,J v]; let p₂ (t:ℝ):= S 2 (d t) ![v,w]; have hV: p₁=ᶠ[𝓝 0] fun t=>star (p₂ t):= ((he.continuousAt).eventually ((conf_open _).mem_nhds (ht.symm ▸ hv))).mono fun t h=>adj_actsT hp hP hφ F HQ x y a b v w t h
       rw [hh]; apply HasDerivAt.unique (f:=p₁) -- signature.
       · simpa only [update1, Matrix.cons_val_one, Matrix.cons_val_zero] using ear_t HQ a (F.adj b w) (F.adj b v) _ (neighbor hp hP hφ F HQ (N y) (N x) hX) z (1:Fin 2) sg hz hg
       apply HasDerivAt.congr_of_eventuallyEq _ hV
       have hR :HasDerivAt p₂ (S 2 x' (![K.arc a v,w])) 0:=by simpa only [one_smul,update0, Matrix.cons_val_zero] using ear_t HQ a v w x' hv d T 1 ht (by simpa only [one_smul] using he)
       exact (by exact hR.star)
end YM.Massive.Tarn.ChargeQ
#print axioms YM.Massive.Tarn.ChargeQ.reversal
