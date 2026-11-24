import YM.Iceberg.Pitch
set_option maxHeartbeats 560000
set_option autoImplicit false
noncomputable section
namespace YM.Lobo
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Iceberg Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open StressFlux (pair curl0)
open Finset
open Massive.Oriole
variable {d:ℕ}(a b:Flavor 6)(p q:Multi d)(M:Bundle)(g:PClan)
local notation "U"=>SpinMode d
set_option quotPrecheck false
local notation "P"=>g a
local notation "Q"=>g b
local notation "Y"=>tileT g false d
local notation "X"=>tileT g true d
local notation "LC"=>wave (g a).matrix.val
local notation "LD"=>wave (g b).matrix⁻¹.val
variable (t u:SpinMode d)
lemma upRow (z:Fiber): (Y) ((q,z),b) u= if b=u.2 then multiMove (g b) q u.1.1*(LD) z u.1.2 else 0:=row_spin .. -- row spin false.L.K def splice
lemma upBar (z:Fiber): (X).transpose t ((p,z),a)= if a=t.2 then multiMove (g a) p t.1.1*(LC) t.1.2 z else 0:=by
     rw [Matrix.transpose_apply,row_spin]; unfold UV.turned; rw [Matrix.of_apply]; change _=_; split
     · next h=>change multiMove _ _ _*wave (g a).matrix.val.transpose z t.1.2=_; rw [UV.wave_tr]; rfl
     · next he=> rfl
-- collapse Fibers with constants. primitive larger support general PA. Want across ALL. allows p q charged f != etc. maybe.
lemma hovering(T:Matrix U U ℂ) : (T.transpose*fieldB a b p q M) t u= ∑ i:Fiber, ∑ j:Fiber, T ((p,i),a) t*(if u=((q,j),b) then M i j else 0):=by
      unfold fieldB; rw [Matrix.mul_apply]; simp_rw[Matrix.sum_apply]; simp_rw [Finset.mul_sum]; rw[sum_comm]; refine sum_congr rfl fun i _=>?_ ; rw[sum_comm]; refine sum_congr rfl fun j _=>?_ ; rw [sum_eq_single ((p,i),a)]
      · simp only[Matrix.transpose_apply,Matrix.single_apply]; by_cases h:u=((q,j),b) <;> simp [h,eq_comm]
      · intro k _ h; simp [Matrix.single_apply,h,h.symm]
      simp
lemma puff(T S:Matrix U U ℂ) :(T.transpose*(fieldB a b p q M*S)) t u= ∑ i:Fiber,∑ j:Fiber, T ((p,i),a) t * M i j * S ((q,j),b) u:=by
      rw[← mul_assoc, Matrix.mul_apply]; simp_rw [hovering, Finset.sum_mul]; rw [sum_comm]; apply sum_congr rfl; intro i _; rw [sum_comm]; apply sum_congr rfl; intro j _; simp [mul_ite,ite_mul]
private lemma matU (L R C: Bundle) {c d:Flavor 6} (u v: Fiber)(x y:ℂ): (∑ i:Fiber,∑ j:Fiber,(if a=c then x * L u i else 0) * (C i j) * (if b=d then y * R j v else 0))= if c=a∧d=b then x*y*(L*(C*R)) u v else 0:=by
     by_cases h:c=a; swap; · simp only [if_neg (Ne.symm h),h,false_and,↓reduceIte,zero_mul,sum_const_zero]
     by_cases he:d=b; swap; · simp only[if_neg (Ne.symm he),mul_zero,sum_const_zero,he,and_false,↓reduceIte]
     rw [if_pos ⟨h,he⟩]; simp only [if_pos h.symm,if_pos he.symm,Matrix.mul_apply,Finset.mul_sum]; apply sum_congr rfl; intro x _; apply sum_congr rfl; intro y _; ring
lemma filled (E W :Matrix U U ℂ)(r v:Multi d →ℂ)(L R:Bundle)
  (hE:∀ t:SpinMode d,∀ z:Fiber,E.transpose t ((p,z),a)= if a=t.2 then r t.1.1*L t.1.2 z else 0)
  (hW:∀ t:SpinMode d,∀ z:Fiber,W ((q,z),b) t= if b=t.2 then v t.1.1*R z t.1.2 else 0) : E.transpose*(fieldB a b p q M*W)=∑ i: Multi d,∑ j:Multi d, (r i*v j) • fieldB a b i j (L*(M*R)):=by
    have he(t u:SpinMode d):(E.transpose*(fieldB a b p q M* W)) t u = if t.2=a∧u.2=b then r t.1.1*v u.1.1*(L*(M*R)) t.1.2 u.1.2 else 0:=by
              have hh(i:Fiber): E ((p,i),a) t=(if a=t.2 then r t.1.1*L t.1.2 i else 0):= hE t i; rw [puff]; simp_rw [hh,hW]; exact matU a b _ _ M _ _ _ _
    ext t u; rw [he]; simp_rw [Matrix.sum_apply,Matrix.smul_apply,fieldK]; split
    · next h => rw [sum_eq_single t.1.1,sum_eq_single u.1.1]; · rw[if_pos ⟨rfl,h.1,rfl,h.2⟩]; rfl
                · intro i _ he; rw [if_neg (fun h=>he h.2.2.1.symm),smul_zero]
                · simp
                · intro j _ he; apply sum_eq_zero; intro k _; rw [if_neg (fun h=>he h.1.symm),smul_zero]
                simp
    · next h => symm; refine sum_eq_zero fun i _=>sum_eq_zero fun j _=>?_ ; rw[if_neg (fun p=>h ⟨p.2.1,p.2.2.2⟩),smul_zero]
lemma rollsK : spun g d (Oriole.coat (fieldB a b p q M))= ∑ i:Multi d,∑ j:Multi d,(multiMove P p i*multiMove Q q j) • Oriole.coat (fieldB a b i j (LC*(M*LD))):=by
     simp_rw [← map_smul,← map_sum]; unfold spun; change Grass.adapter _ _ (-form _)= _; rw [map_neg,form_map]; change Oriole.coat ((X).transpose* _)= _; exact congr_arg Oriole.coat (filled a b p q M _ _ _ _ _ _ (upBar a p g) (upRow b q g))
end YM.Lobo
#print axioms YM.Lobo.rollsK
