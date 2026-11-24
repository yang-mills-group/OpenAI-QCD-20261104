import YM.Avian.Attain
/-! Family parity/charge and differentiation, movement at axial origin in K-score. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Rolls
open Function Lattice RG Wilson Filter Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator Classical
open Cylinder QCD QCD.Lat QCD.Grass UV Patria Patria.Depth Patria.Exposure Patria.Hub Poised Poised.Plans Poised.Plans.Stamp Gall Intag MassFields
open Lining Lining.Temper
variable {S:Scheme}{R:Side}{i N p n d D:ℕ}{A:Run S N R 6}{T:SourceRead.TaperHol}(sym:RawSym)(B:Bore d)(hT:Rubric sym B)(W:Market S R d)(hW:Wager A T B W 0)
namespace Attain
variable {M:Type}[Fintype M] (S:Side)(U V:Averaging)
variable (F:M → Cover→Insertion S 6)(X Y: Cover→Insertion S 6)(s:Signed)(a:Axis) (T:Lat.Fields S 6→ₐ[ℂ] Lat.Fields S 6)
local notation "L"=> Lattice.step a
variable (r t:ℝ)
lemma highE (Z:ℂ)(e v:Grid S)(h:∀ x:Cover,T (X x v) = (Z*((↑(signT s a):ℂ))) • Y (s.act x) e) (p:Cover) : T ((nick t a X p) v)= Z • ((nick t (s.perm a) Y (s.act p)) e):=by
     have hR(i:Axis): (s.act (Lattice.step i):Cover)= if s.flip i then -(step (s.perm i)) else step (s.perm i):= by rw [← Step.vec_pos,← Step.vec_rotate]; simp [Step.vec,Step.rotate,posDir]
     let Q(y:Cover):= (Y y) e; change T ((↑(t/2):ℂ) • (X (p+L) v-X (p-L) v))= Z • ((↑(t/2):ℂ) • (Q (s.act p+ _)-Q (s.act p - _))); rw [map_smul,map_sub,h,h,Signed.act_add,Signed.act_sub,hR]; unfold signT; split; next h=> simp only[Complex.ofReal_neg,Complex.ofReal_one,mul_neg, mul_one, neg_smul,sub_neg_eq_add,← sub_eq_add_neg]; unfold Q; module
     next h=> simp only [Complex.ofReal_one,mul_one]; unfold Q; module
lemma aux_val (f g: Grid S)(z:Cover)(e:M≃M)(A B:M → Cover→Insertion S 6)(h:∀ i x,T ((A i x) f) =r • ((B (e i) (s.act x)) g)): T ((∑ i:M,A i) z f)= r • (∑ i:M,B i) (s.act z) g:=by rw [Finset.sum_apply,Finset.sum_apply, ContinuousMap.sum_apply, ContinuousMap.sum_apply]; rw[map_sum]; simp_rw[h]; rw [← Finset.smul_sum]; apply congr_arg; exact Equiv.sum_comp e (fun i=> B i (s.act z) g) -- `sum_apply` direction
lemma aux_g (J K:Grid S)(Z:Cover)(h:∀ x:Cover,T (X x J)=X x K): T ((nick t a X Z) J)=nick t a X Z K:=by
    change T ((↑(t/2):ℂ) • (_-_))= (↑(t/2):ℂ) • (_-_); rw [map_smul,map_sub,h,h] -- typeclass error
end Attain
end YM.Massive.Patria.Rolls
#print axioms YM.Massive.Patria.Rolls.Attain.highE
