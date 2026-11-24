import YM.Kauri.Step
set_option autoImplicit false
noncomputable section
namespace YM.Kauri
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder InnerProductSpace Matrix.Norms.Frobenius
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates Mako Lobo
open Ortho (plane Skew)
open Tawny Tawny.Cast Perla Carnal
open Finset
variable (s:EuPin)(u:Ortho) (a b:Axis)
lemma vert : ∑ i:Axis,u.val a i*u.val b i= if a=b then 1 else 0:=by
       have hv:= congr_fun (congr_fun (show u.val *star u.val=1 from u.property.2) a) b; simpa [Matrix.star_eq_conjTranspose,Matrix.one_apply, Matrix.mul_apply] using hv
lemma horiz: ∑ i:Axis,u.val i a*u.val i b=if a=b then 1 else 0:=by
       have h:= vert u⁻¹ a b; exact h
lemma paint : putH (s,plainPicture s) 8 (spire.val (a,b))=∑ i:Axis,∑ j:Axis,(↑(s.coord.val i a*s.coord.val j b):ℂ) • spire.val (i,j):=by
       simp_rw [spire_val,map_sum,putG]; let P:=s.coord.val; let G(i j k l m:Axis):Label 8:=(↑(P i a*P j k*(P l b*P m k)):ℂ) • GG i j l m
       have ht(i j l m:Axis): (∑ k:Axis,G i j k l m)=if j=m then (↑(P i a*P l b):ℂ) • (GG i j l m) else 0:=by
                 unfold G; simp_rw [show ∀ k:Axis,P i a*P j k*(P l b*P m k)= (P i a*P l b)*(P j k*P m k) from fun i=>by ring,← sum_smul,←Complex.ofReal_sum,← mul_sum,show ∑ i:Axis,P j i*P m i=_ from vert s.coord j m]; split <;> simp [*]
       have hh(i:Axis): (∑ k:Axis, ∑ j:Axis,∑ l:Axis,∑ m:Axis,G i j k l m)=∑ j:Axis,∑ l:Axis,∑ m:Axis,∑ k:Axis,G i j k l m:=by
                 rw [sum_comm]; apply sum_congr rfl; intro j _; rw [sum_comm]; apply sum_congr rfl; intro l _; exact sum_comm
       change (∑ k:Axis,∑ i:Axis, ∑ j:Axis,∑ l:Axis,∑ m:Axis,G i j k l m)=_; rw [sum_comm]; simp_rw[hh,ht,smul_sum]; apply sum_congr rfl; intro i _; rw[sum_comm]; simp[P]
lemma peakW : putH (s,plainPicture s) 8 (eclipse.val (a,b))= ∑ i:Axis,∑ j:Axis,(↑(s.coord.val i a*s.coord.val j b):ℂ) • eclipse.val (i,j):=by
       let P:=s.coord.val; let L:=∑ i:Axis, spire.val (i,i); have hp : putH (s,plainPicture s) _ L=L:=by
                  simp_rw [L,map_sum,paint]; rw [sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [sum_comm]; simp_rw [←sum_smul, ←Complex.ofReal_sum, vert]; simp [ite_smul,apply_ite]
       simp_rw [show ∀ i j:Axis,eclipse.val (i,j)= if i=j then L else 0 from fun i j=> dark ..]; simp only [smul_ite,smul_zero,sum_ite_eq, Finset.mem_univ,↓reduceIte]; rw [←sum_smul,←Complex.ofReal_sum,horiz]; split <;> simp [*,hp]
lemma twoflags {V:Type*}[AddCommGroup V][Module ℂ V](F:Module.End ℂ V)(g h:Axis→Axis→ V)(r:ℂ)
   (hg:F (g a b)= ∑ i:Axis,∑ j:Axis, (↑(s.coord.val i a*s.coord.val j b):ℂ) • g i j) (hh:F (h a b)= ∑ i:Axis,∑ j:Axis,(↑(s.coord.val i a*s.coord.val j b):ℂ) • h i j): F (g a b-r • h a b)=∑ i:Axis,∑ j:Axis,(↑(s.coord.val i a*s.coord.val j b):ℂ) • (g i j-r • h i j):=by
             rw [_root_.map_sub,map_smul,hg,hh]; simp_rw [smul_sub,sum_sub_distrib]; apply congr_arg₂ _ rfl; simp_rw [smul_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; exact smul_comm ..
lemma marble : pinAct s (gaugeStress a b)= ∑ i:Axis,∑ j:Axis,(↑(s.coord.val i a*s.coord.val j b):ℂ) • gaugeStress i j:=by
     let v:=(s,plainPicture s); have he: putH v _ (solid.val (a,b))=∑ i:Axis,∑ j:Axis,(↑(s.coord.val i a*s.coord.val j b):ℂ) • (solid.val (i,j)):=by
             exact twoflags s a b (putH v 8).toLinearMap (fun a b=>spire.val (a,b)) (fun a b=>eclipse.val (a,b)) (1/4:ℂ) (paint s a b) (peakW s a b)
     rw[← spine_pin]; simp_rw [← gauge_val]; have ht:= congr_arg Subtype.val he; simp_rw [AddSubmonoidClass.coe_finsetSum,Submodule.coe_smul] at ht; exact ht
-- Clifford covar
variable {d:ℕ}(f:Flavor 6)
lemma gammaC : Euv (plainPicture s) f f (gamma a)=∑ i:Axis,(s.coord.val i a:ℂ) • gamma i:=by
       change s.matrix.val*(gamma a*s.matrix⁻¹.val)=_; rw[←mul_assoc,s.act_gamma,mul_assoc,show s.matrix.val*s.matrix⁻¹.val=1 from s.matrix.val_inv,mul_one]; unfold Massive.slash Ortho.move; simp
lemma primes (p q:Multi d) : ∃ L:Spike→ₗ[ℂ] Pol d, ∀ x,L x=bilinear f f x p q:=by
       refine ⟨{toFun:=fun x=>bilinear f f x p q,map_add':=fun x y=>?_,map_smul':=fun r x=>Massive.Oriole.nourish f f ..},fun x=>rfl⟩
       unfold bilinear; simp only [Matrix.add_apply, add_smul,sum_add_distrib]; exact TensorProduct.tmul_add ..
lemma sap : pinAct s (spinStressUnsymm f a b)=∑ i:Axis,∑ j:Axis,(↑(s.coord.val i a*s.coord.val j b):ℂ) • spinStressUnsymm f i j:=by
      choose L hL using fun p q:Multi 8=> primes f p q; rw [sum_comm]; unfold spinStressUnsymm; simp_rw[map_sub,←spine_pin,sigA,sigP, gammaC]; change (∑ i:Axis,(s.coord.val i b:ℂ) • _)-(∑ i:Axis,(s.coord.val i b:ℂ) • _) = _; simp_rw [← hL,map_sum,map_smul, smul_sum,smul_sub,sum_sub_distrib, smul_smul]; simp_rw [mul_comm _ (s.coord.val _ b),Complex.ofReal_mul]
lemma firm: pinAct s (totalStress a b)=∑ i:Axis,∑ j:Axis,(↑(s.coord.val i a*s.coord.val j b):ℂ) • totalStress i j:=by
      let L(i j:Axis)(f:Flavor 6):= spinStressUnsymm f i j+spinStressUnsymm f j i; let v(c:Flavor 6):= (fun i:Axis=>fun j:Axis=> (1/4:ℂ) • L i j c); have he(c): pinAct s (L a b c)= ∑ i:Axis,∑ j:Axis,(↑(s.coord.val i a*s.coord.val j b):ℂ) • L i j c:=by
             simp only[L,map_add,sap,smul_add,sum_add_distrib]; apply congr_arg₂ _ rfl; rw[sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw[mul_comm]
      unfold totalStress; change pinAct s (gaugeStress .. + _)= _; rw[map_add,marble,map_smul]; change _+(1/4:ℂ) • pinAct s (∑ c:Flavor 6,L a b c)=∑ i:Axis,∑ j:Axis,(↑(s.coord.val i a*s.coord.val j b):ℂ) • (_ +(1/4:ℂ) • (∑ c:Flavor 6,L i j c)); rw[map_sum]; simp_rw [he,smul_add,sum_add_distrib]; apply congr_arg₂ _ rfl; simp_rw[smul_sum]; rw [sum_comm]; apply sum_congr rfl; intro i _; rw [sum_comm]; apply sum_congr rfl; intro j _; apply sum_congr rfl; intro c _; exact smul_comm ..
lemma realA (σ:RawSym)(R:Roof σ) : caravan R 8 s (projection ((bendP (fun _=>1)).val (a,b)))= ∑ i:Axis,∑ j:Axis,(↑(s.coord.val i a*s.coord.val j b):ℂ) • projection ((bendP (fun _=>1)).val (i,j)):=by
       rw [clanP]; simp_rw [←map_smul, ←map_sum]; apply congr_arg; apply Subtype.ext; rw [σ.pinActs,magic,map_neg]; simp_rw [AddSubmonoidClass.coe_finsetSum,Submodule.coe_smul, magic,smul_neg,sum_neg_distrib]; rw [firm]
end YM.Kauri
#print axioms YM.Kauri.realA
