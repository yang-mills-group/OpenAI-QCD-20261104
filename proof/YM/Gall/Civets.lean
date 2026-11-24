import YM.Gall.Vest
/-! Explicit projection tables. Use only requests needed for DS bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny.Cast.Rays
variable {u t a D C v e s:ℝ}{c:Side}{n l d m r w b:ℕ}{U:BudgetPoint}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC
open QCD.Entr.Goals
local notation "Q"=> (0:Multi 10)
local notation "Y"=> (0:Multi 8)
local notation "E"=> ηR
local notation "J"=> leadR
local notation "D"=> (1/2:ℝ)
variable (x y z: Axis)(p:Cover)
lemma leadW : power (J x) y= if x=y then 1 else 0:=by by_cases h:x=y <;> simp [power,leadR,h]
lemma ears : power (E x y) z= power (J x) z+power (J y) z:=by
      change Function.update (power (J x)) y _ z= _; rw [leadW y z]; by_cases h:y=z; subst z; rw[if_pos rfl,Function.update_self]
      rw[Function.update_of_ne (Ne.symm h),if_neg h,add_zero]
lemma profile_L: profile (J x) p 1=(p x:ℂ):=by
      unfold profile; rw[one_pow,one_mul,prod_eq_single x]; rw [leadW,if_pos rfl]; simp
      intro i _ h; rw[leadW,if_neg (Ne.symm h)]; simp
      simp
lemma profile_C : profile (E x x) p 1=(p x:ℂ)^2/2:=by
     unfold profile; rw [one_pow,one_mul,prod_eq_single x]; rw [ears,leadW,if_pos rfl]; norm_num
     intro i _ h; rw[ears,leadW,if_neg (Ne.symm h)]; simp
     simp
lemma profile_N (h:x≠y): profile (E x y) p 1=(p x:ℂ)*(p y:ℂ):=by
     unfold profile; let f i:=(p i:ℝ)^(power (E x y) i)/ Nat.factorial (power (E x y) i)
     rw [one_pow,one_mul,← mul_prod_erase (s:=Finset.univ) (f:=f) (mem_univ x),prod_eq_single y]; simp [f,ears,leadW,h,Ne.symm h]
     intro i hi h; unfold f; rw[ears,leadW,if_neg (Ne.symm (ne_of_mem_erase hi)),leadW,if_neg (Ne.symm h)]; simp
     simp [Ne.symm h]
-- maps weigh origin
variable (T:TaperHol)(u v: Site c)(i j:Pinor)(k: Axis)
local notation "K"=> step (S:=ℤ) k
local notation "t"=> T.T
local notation "Eℓ" p:arg q:arg=>ballast p q T.T
local notation "pW" p:arg q:arg=> D • (beamT (c:=c) T.T p q K - beamT (c:=c) T.T p q (-K))
noncomputable def piv (i j:Axis):ℂ:= if i=j then 1 else 0
lemma oval : pW Q Q= (0: Site c→Site c→ℂ):=by
      funext u v; simp[beamT,bias,profile_0] -- notation can't simp
lemma ivoryB : pW Q (J x)= piv x k • Eℓ Y Y :=by
      funext u v; simp only [Pi.smul_apply,Pi.sub_apply,beamT,bias,ballast,Nw, profile_L,profile_0, Pi.add_apply, Pi.neg_apply, step_apply]; by_cases h:x=k
      · subst k; simp[piv]; ring
      simp [h,piv]
lemma ivoryC : pW Q (E x x)= piv x k • Eℓ Y (UV.first x):=by
      funext u v; simp only [Pi.smul_apply,Pi.sub_apply,beamT,bias,ballast,Nw,profile_0,profile_C,profile_1,Pi.add_apply,Pi.neg_apply,step_apply]; by_cases h:x=k
      · subst k; simp [piv]; ring
      simp[h,piv]
lemma ivoryN (h:x≠ y) : pW Q (E x y)= piv x k • Eℓ Y (UV.first y)+ piv y k • Eℓ Y (UV.first x):=by
      funext u v; simp only [Pi.smul_apply,Pi.sub_apply, Pi.add_apply,beamT,bias,ballast,Nw,profile_0,profile_N x y _ h,profile_1,Pi.add_apply,Pi.neg_apply,step_apply]; by_cases hx:x=k
      · subst k; simp[piv,h,h.symm]; ring -- h.symm
      by_cases hy:y=k
      · subst k; simp[piv,h]; ring
      simp[piv,hx,hy]
lemma ivoryV : pW (J x) (J y)= piv x k • Eℓ Y (UV.first y) + piv y k • Eℓ (UV.first x) Y:=by
      funext u v; simp only[Pi.smul_apply,Pi.sub_apply, Pi.add_apply, beamT,bias,ballast,Nw, profile_0,profile_1,profile_L,Pi.add_apply,Pi.neg_apply,step_apply]; by_cases hx:x=k
      · subst k; by_cases hy:y=x; · subst y; simp [piv]; ring
        simp [piv,hy]; ring
      by_cases hy:y=k
      · subst k; simp [piv,hx]; ring
      simp[piv,hx,hy]
variable (G F: Density c 6)(g: Flavor 6)
local notation "gQ" p:arg q:arg x:arg=> loaf p q g i j x
variable (Z:Label 8)(X:Label 10)(H:Tutor 0 U (foil G F) a n m C)(hP:Tally T 0 X G (stunt k F))(hF:Tally T 0 Z G F)(ha:0<a)(hn:3≤ n)(hm:2 < m)(hG:∀ x:Cover,march x G=G)
local notation "vX"=>foil G F 1
local notation "H'"=> port C c a
include hP hF hG hn hm ha H
lemma impetus : ‖gQ Q (J x) X-piv x k*gQ Y Y Z‖≤ H':=by
     have h:=instant Q (J x) T k g i j F G X H hP ha hm hn hG (le_refl 10) (by rw[gradeV,gradeL]; norm_num); rw [notice Q (J x) T k g i j vX,ivoryB x T k,entire_c] at h; rwa [scan Y Y T g i j G F Z hF (by rw[cost_root]; norm_num)]
lemma meanV : ‖gQ Q (E x x) X-piv x k*gQ Y (UV.first x) Z‖≤ H':=by
     have h:=instant Q (E x x) T k g i j F G X H hP ha hm hn hG le_rfl (by rw[gradeV,gradeH]); rw [notice Q (E x x) T k g i j vX,ivoryC x T k,entire_c] at h; rwa [scan Y (UV.first x) T g i j G F Z hF (by rw[cost_root,juicy])]
lemma meanP (h:x≠y) : ‖gQ Q (E x y) X-(piv x k*gQ Y (UV.first y) Z+piv y k*gQ Y (UV.first x) Z)‖≤ H':=by
     have hv:=instant Q (E x y) T k g i j F G X H hP ha hm hn hG le_rfl (by rw[gradeV,gradeH]); rw [notice Q (E x y) T k g i j vX,ivoryN x y T k h,entire,entire_c,entire_c] at hv; rw[scan Y (UV.first y) T g i j G F Z hF (by rw [cost_root,juicy]), scan Y (UV.first x) T g i j G F Z hF (by rw [cost_root,juicy])]; exact hv -- ambiguous first
lemma meanD : ‖gQ (J x) (J y) X-(piv x k*gQ Y (UV.first y) Z+piv y k*gQ (UV.first x) Y Z)‖≤ H':=by
     have hv:=instant (J x) (J y) T k g i j F G X H hP ha hm hn hG le_rfl (by rw[gradeL,gradeL]); rw [notice (J x) (J y) T k g i j vX,ivoryV x y T k,entire,entire_c,entire_c] at hv; rw [scan Y (UV.first y) T g i j G F Z hF (by rw [cost_root,juicy]), scan (UV.first x) Y T g i j G F Z hF (by rw [cost_root,juicy])]; exact hv
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.meanD
#print axioms YM.Massive.Patria.Gall.meanP
#print axioms YM.Massive.Patria.Gall.meanV
#print axioms YM.Massive.Patria.Gall.impetus
