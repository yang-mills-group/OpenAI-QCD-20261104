import YM.Lobo.Rive
import YM.Lobo.Perch
set_option maxHeartbeats 580000
set_option autoImplicit false
noncomputable section
namespace YM.Lobo
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Massive.Oriole
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open Finset
variable (k i j:Tri)(t:ℝ)(G:EuPin)(he:G.coord= Thr k t)
local notation "X"=> lieu k
local notation "Y"=> lieu (edgeK k)
local notation "Z"=> lieu (backK k)
variable (u w:Bool)
include he
lemma gall : conjug G (gamma (lieu i))= wing k t (fun j=>gamma (lieu j)) i:=by rw [tarG,he]; exact hat k i t _
omit he
private lemma wRing (f g:Spike)(s c:ℂ)(h:c^2+s^2=1)(hx:f*f=1)(hy:g*g=1)(hf:g*f=-(f*g)): (c • f+s • g)*(c • g - s • f)= f*g:=by
     rw [add_mul,mul_sub,mul_sub]; simp only [Matrix.smul_mul,Matrix.mul_smul,hx,hy,hf]; simp only[smul_smul, smul_neg]; -- rw to identity
     generalize hn:(1:Spike)=x; generalize hk:f*g=y; calc
        _=(c^2+s^2) • y:=by module
        _=_:=by rw[h,one_smul]
include he
lemma heatG : conjug G (gamma Y*gamma Z)=gamma Y* gamma Z:=by
    rw[L_up]; rw[gall k _ t G he,gall k _ t G he,(wingsI ..).2.1,(wingsI ..).2.2]; refine wRing (gamma Y) (gamma Z) _ _ ?_ (Lat.gamma_sq Y) (Lat.gamma_sq Z) (Lat.clifford (fun h=>threeL k (Fin.castSucc_inj.1 h))); rw [← Complex.ofReal_pow,← Complex.ofReal_pow,← Complex.ofReal_add, add_comm,Real.sin_sq_add_cos_sq,Complex.ofReal_one]
omit he
lemma swap3 (a b c:Axis)(h:a≠b)(hx:a≠c):gamma a*(gamma b*gamma c)=gamma b*(gamma c*gamma a):=by rw[← mul_assoc,Lat.clifford h,neg_mul,mul_assoc,Lat.clifford hx, mul_neg,neg_neg]
lemma foamy : gamma 0*(gamma 1*gamma 2)= gamma X*(gamma Y* gamma Z):=by
      fin_cases k; rfl; exact swap3 0 1 2 (by decide) (by decide)
      exact (swap3 2 0 1 (by decide) (by decide)).symm
include he
lemma azure : conjug G (flat (none,u,w))= flat (none,u,w):=by
      have ht:conjug G (gamma timeAxis)=gamma timeAxis:=by rw[tarG,he]; exact lastB k t _
      let M:= gamma 0*(gamma 1*gamma 2); have h : conjug G M=M:=by unfold M; rw[foamy k,L_up,heatG k t G he,gall k k t G he,(wingsI k t _).1]
      cases u<;>cases w
      · change conjug G 1=1; unfold conjug; rw[mul_one]; exact G.matrix.val_inv
      · convert ht using 1 <;> simp [flat,pearl,gait,ride,flair]
      · simpa only[flat,pearl, gait,ride,flair, List.map_cons,List.prod_cons,mul_one, List.map_nil,List.prod_nil,List.append_nil,Option.elim, ↓reduceIte,Bool.false_eq_true] using h
      rw [show flat (none,true,true)=M* gamma timeAxis from (by unfold M flat pearl gait ride flair; simp [mul_assoc]),L_up,h,ht]
lemma chrome : conjug G (flat (some i,u,w))= wing k t (fun i=>flat (some i,u,w)) i:=by
      have h (i:Tri) : flat (some i,u,w)= gamma (lieu i)* flat (none,u,w):=rfl
      rw [h,L_up,gall k i t G he,azure k t G he]; simp_rw [h]; unfold wing; rw[Matrix.sum_mul]; apply sum_congr rfl; intro j _; rw [Matrix.smul_mul]
end YM.Lobo
#print axioms YM.Lobo.chrome
