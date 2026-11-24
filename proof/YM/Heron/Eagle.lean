import YM.Heron.Thr
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice Maxwell.Free
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix
open Maxwell (grad away open_away)
open Arise.Range
variable {d e:ℕ}(t w:Bool)(p:Multi d)(q:Multi e)(i j:Pinor)(a b: Hue)(u v:QCD.Flavor 6)(x y:E4)
noncomputable def bond {d:ℕ}(t:Bool)(p:SpinMode d):letters d:= if t then Sum.inr p else Sum.inl p
noncomputable def linked (x y:E4)(s:letters d)(q:letters e):ℂ:=
   Sum.elim (fun v => Sum.elim (fun _ => 0) (fun q=> UV.Free.leg v q x y) q) (fun v=> Sum.elim (fun q=> -UV.Free.leg q v y x) (fun _=> 0) q) s
lemma stapled (s:letters d)(q:letters e): Hail.atP (points ![x,y]) s q=linked x y s q:= by rcases s with s|s <;> rcases q with q|q <;> rfl
noncomputable def code(t:Bool)(p:Multi d)(i:Pinor)(a:Hue)(u:QCD.Flavor 6):= bond t ((p,i,a),u)
local notation "P"=> code t p i a u
local notation "Q"=> code (!t) q j b v
lemma blank: linked x y P (code t q j b v)=0:=by cases t<;>rfl
lemma flying : linked x y P Q=-linked y x Q P:=by cases t<;> simp [code,bond,linked]
lemma lowSt(h:¬(a=b ∧ u=v)): linked x y P Q=0:=by
   have hv:¬(b=a∧ v=u):=fun he=> h ⟨he.1.symm,he.2.symm⟩;
                                                            cases t <;> simp [code,bond,linked,UV.Free.leg,h,hv]
local notation "L"=> steps p
local notation "M"=> steps q
local notation "V"=> pose (formT t) (deck i)
variable (h:x ≠ y)
include h
private lemma perm_power (d e:ℕ) : -((-1:ℂ)^d) *(-1)^(d+e+1)=(-1)^e:=by
    rw [pow_add,pow_add, pow_one]; have hp:(-1:ℂ)^d * (-1)^d=1:=by rw[← sq,←pow_mul,mul_comm d,pow_mul]; simp; -- goal nested rw?
    calc _=(((-1:ℂ)^d * (-1)^d))*(-1)^e:=by ring
         _=_:=by rw[hp,one_mul]
lemma hook (he:a=b∧u=v): linked x y P Q = deriveL (steps q) (pose (formT t) (deck i) (steps p) x) y j:=by
    obtain ⟨rfl,rfl⟩:=he; rw [pearls]; -- implicit h
    · change _= ((-1:ℝ)^(steps q).length) • deriveL (M++L) (hull (formT t) (deck i)) (x-y) j
      rw[able t i j _ (M++L) (sub_ne_zero.mpr h)]; cases t
      · change UV.Free.leg ((p,i,a),u) ((q,j,a),u) x y= (-1:ℝ)^(steps q).length • _; unfold UV.Free.leg; rw[if_pos (And.intro rfl rfl)]; rw[Complex.real_smul]; simp only [Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]; exact congr_arg (_ * ·) (commute_a open_away _ (is_hot i j) _ _ (List.perm_append_comm ..) (x-y) (sub_ne_zero.mpr h))
      · change -UV.Free.leg ((q,j,a),u) ((p,i,a),u) y x=(-1:ℝ)^(steps q).length • derivatives _ _ _; unfold UV.Free.leg; rw[if_pos (And.intro rfl rfl)]; rw[perP j i _ _ (sub_ne_zero.mpr h.symm), show -(y-x)=x-y from neg_sub y x, Complex.real_smul]; simp only [List.length_append,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]; -- exponent order
        rw [← mul_assoc,← neg_mul,add_comm (steps q).length (steps p).length, ← neg_mul, perm_power x y h]
    all_goals exact h
lemma stemZ(r:Multi d)(h':r= (0:Multi d)): steps r =[]:=by subst r; unfold steps; simp [show ∀ i,power (0: Multi d) i=0 from fun i=>rfl]
lemma tag_p (r:Axis): steps (UV.first r)=[r]:=by -- Hail.Hour
    have hh:AtNext r (0:Multi 8) (UV.first r):=by rw [AtNext,← Hail.stemR]; exact Massive.Tawny.Cast.Rays.add_zeroL _
    have he:= DawnS.permutation hh; rw[stemZ (d:=8) x y h _ rfl] at he; exact List.perm_singleton.mp he
end YM.Heron
#print axioms YM.Heron.hook
#print axioms YM.Heron.tag_p
