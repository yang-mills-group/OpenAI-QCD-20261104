import YM.Vern.Pier
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Set Function Filter
open scoped Topology BigOperators Classical ComplexOrder InnerProductSpace
open Vern
-- operations
abbrev clip {R:Type*}[Ring R](x y:R):R:=x*y-y*x
lemma jac {R:Type*}[Ring R](x y z:R):clip (clip x y) z=clip (clip x z) y+clip x (clip y z):=by unfold clip; noncomm_ring
variable {W:Type*}[AddCommGroup W][Module ℂ W](S:Tide W)(f g:Module.End ℂ W)
lemma lplus(h:S.Leans f)(hx:S.Leans g): S.Leans (f+g):=by
     intro u v; rw[LinearMap.add_apply,S.other,h,hx,LinearMap.add_apply,S.add,neg_add]
lemma lneg(h:S.Leans f): S.Leans (-f):=by intro u v; rw[← neg_one_smul ℂ,LinearMap.smul_apply,LinearMap.smul_apply,S.seals,S.sep,h]; simp
lemma lclip(h:S.Leans f)(hx:S.Leans g): S.Leans (clip f g):=by
     intro u v; have he(p q:W): S.knot (-p) q= -S.knot p q:=by rw [←neg_one_smul ℂ p,S.seals]; simp
     have hv(p q:W): S.knot p (-q)= -S.knot p q:= (map_neg (S.zz p) q); simp only [clip,sub_eq_add_neg,LinearMap.add_apply,LinearMap.neg_apply,Module.End.mul_apply,S.other,S.add,hv,he]; rw[h (g u),hx (f u),h,hx]; abel
lemma lsub (h:S.Leans f)(hx:S.Leans g): S.Leans (f-g):=by rw[sub_eq_add_neg]; exact lplus S _ _ h (lneg S _ hx)
lemma lzero:S.Leans 0:=by
     intro x y; change S.knot 0 y= -S.knot x 0; rw[S.zero',neg_zero,←S.con y,S.zero',star_zero]
variable [FiniteDimensional ℂ W]
local notation "M"=> Module.End ℂ W
local notation "B0"=> Fin (Module.finrank ℂ W)
def Clear (f:M):Prop:=∃ (B:Module.Basis B0 ℂ W)(a:B0→ℂ),∀ i,f (B i)=a i • B i
lemma band(h:S.Leans f): Clear f:=by
     let c:=S.coreP; letI :InnerProductSpace.Core ℂ W:=c
     letI:NormedAddCommGroup W:=c.toNormedAddCommGroup
     letI:PreInnerProductSpace.Core ℂ W:=c.toCore
     letI:InnerProductSpace ℂ W:=.ofCore c.toCore
     let J:= Complex.I • f; have hj:J.IsSymmetric:=by intro x y; change S.knot (Complex.I • f x) y=S.knot x (Complex.I • f y); rw[S.seals,S.sep,h]; simp
     let B:= hj.eigenvectorBasis (n:=Module.finrank ℂ W) rfl
     let a:= hj.eigenvalues (n:=Module.finrank ℂ W) rfl
     refine ⟨B.toBasis,fun i=>Complex.I⁻¹*(a i:ℂ),fun i=>?_⟩
     have he:J (B i)=(a i:ℂ) • B i:= Module.End.mem_eigenspace_iff.mp (hj.hasEigenvector_eigenvectorBasis rfl i).1; change f (B i)=_ • B i; rw[←smul_smul,← he]; exact (inv_smul_smul₀ Complex.I_ne_zero (f (B i))).symm
lemma studs (B:Module.Basis B0 ℂ W)(a:B0→ℂ)(h:∀ i,f (B i)= a i • B i)(j:B0)(x:W): B.coord j (f x)= a j * B.coord j x:=by
     rw [←B.sum_repr x]; simp only[map_sum,map_smul, h,Module.Basis.coord_apply, Finsupp.smul_apply]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; by_cases he:i=j; · subst j; simp; ring
     simp [he]
lemma vows(h:Clear f)(hv: Commute f (clip f g)):clip f g=0:=by
    obtain ⟨B,a,hB⟩:=h; apply B.ext; intro i; apply B.equivFun.injective; ext1 j; let Q:=clip f g
    have he: (a j-a i)* B.coord j (Q (B i))=0:=by
           have ht:f (Q (B i))=Q (f (B i)):= DFunLike.congr_fun hv.eq (B i)
           rw [hB,map_smul] at ht; rw[sub_mul,sub_eq_zero, ← studs f B a hB,ht,map_smul]; rfl
    change B.coord j (Q (B i))= B.coord j 0; rw[map_zero]; rcases mul_eq_zero.mp he with he|he; · rw [sub_eq_zero] at he; unfold Q clip; rw [LinearMap.sub_apply,Module.End.mul_apply,Module.End.mul_apply,map_sub,hB,map_smul,map_smul,studs f B a hB,he]; exact sub_self _
    exact he
end YM.Mako
#print axioms YM.Mako.band
#print axioms YM.Mako.vows
#print axioms YM.Mako.lclip
#print axioms YM.Mako.lsub
#print axioms YM.Mako.lzero
