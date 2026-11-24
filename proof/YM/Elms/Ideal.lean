import YM.Massive.Target.Wick
import YM.Push.RELAY_MARK.Ideal
/-!
# The initial linear equations generating all invariant rank pivots

Before taking cap, no ambient bound. Include spin columns and rows as independent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass
open scoped Topology BigOperators TensorProduct Pointwise
abbrev Letters (d:ℕ):= Pairs (SpinMode d)
abbrev Covec (d:ℕ):= Seed (Letters d)
abbrev gPoly:= UV.GPol
variable {d:ℕ} {x y: Pol d}
-- Recover hom. color projection by full radial.C
noncomputable def draw (G : Gauge) : Maxwell.WickPol G →ₐ[ℂ] Labels.Pol G:= MvPolynomial.aeval (fun i: Maxwell.Slot G => Push.Mark.literal ((Maxwell.coordinateLeg i).comp Maxwell.gaugeJet.leftInverse))
lemma draw_value (G: Gauge) (X:Maxwell.WickPol G)(J:Labels.Jet G): Labels.read J (draw G X) = Maxwell.probe (fun i=>(Maxwell.gaugeJet (G:=G) (j:=i)).leftInverse (J i)) X:=by
   apply DFunLike.congr_fun (f:=(Labels.read J).comp (draw G)) (g:=Maxwell.probe (fun i=>(Maxwell.gaugeJet (G:=G) (j:=i)).leftInverse (J i))) ?_ X; ext i
   rw [AlgHom.comp_apply,draw,MvPolynomial.aeval_X,Push.Mark.read_literal,Maxwell.probe, MvPolynomial.aeval_X]; rfl
lemma draw_erase (G : Gauge) (X : Labels.Pol G) : draw G (Maxwell.reduceEq X)=Labels.changed (Push.Mark.eraseShell G) X:=by apply Labels.eval_ext; intro J; rw [draw_value,Maxwell.jet_value,Labels.eval_changed]; rfl
-- ideal payments
variable (T : Submodule ℂ (Pol d))(X : Push.Mark.Ink su)
def petal (p: Letters d) : Covec d:= Sum.elim (@Free.slashCol d) (@Free.slashBar d) p
lemma garden : slashEq d=Submodule.span ℂ (Set.range (petal (d:=d))):=by
   unfold slashEq; congr 1; ext i; constructor
   · rintro (⟨v,rfl⟩|⟨v,rfl⟩); exact ⟨Sum.inl v,rfl⟩; exact ⟨Sum.inr v,rfl⟩
   rintro ⟨v,rfl⟩; cases v with
   | inl a=>left; exact ⟨a,rfl⟩
   | inr b=>right; exact ⟨b,rfl⟩
abbrev coarse (d:ℕ)(x:gPoly):Pol d:=x⊗ₜ[ℂ](1:SpinPol d)
abbrev flora (x: SpinPol d): Pol d:=(1:gPoly) ⊗ₜ[ℂ] x
lemma coarseL : ∃ L:gPoly→ₗ[ℂ] Pol d, (⇑L)=coarse d:=⟨(Algebra.TensorProduct.includeLeft).toLinearMap,rfl⟩
lemma coarse_at (x y:gPoly)(d:ℕ) : coarse d (x*y) = coarse d x * coarse d y:=by simp [coarse,Algebra.TensorProduct.tmul_mul_tmul]
lemma floraL : ∃ L: SpinPol d→ₗ[ℂ] Pol d,(⇑L)=flora:=⟨(Algebra.TensorProduct.includeRight).toLinearMap,rfl⟩
lemma flora_at (x y: SpinPol d): flora (x*y)=flora x*flora y:=by simp [flora,Algebra.TensorProduct.tmul_mul_tmul]
lemma combo (x:gPoly)(y:SpinPol d): x⊗ₜ[ℂ] y = coarse d x*flora y:=by simp [coarse,flora,Algebra.TensorProduct.tmul_mul_tmul]
lemma combo' (x:gPoly)(y:SpinPol d): x⊗ₜ[ℂ] y = flora y*coarse d x:=by simp [coarse,flora,Algebra.TensorProduct.tmul_mul_tmul]
local notation "φ" =>Labels.changed (Push.Mark.eraseShell su)
lemma gaugeJobs (p:gPoly) (h :∀ X:Push.Mark.Ink su, Push.Mark.Gap X →∀ y:Pol d, coarse d (Push.Mark.literal X.2) * y∈T) :∀ y:Pol d, coarse d (p-φ p)*y∈ T:=by
   obtain ⟨f,hf⟩:=coarseL (d:=d); induction p using MvPolynomial.induction_on with
   | C a=> intro y; simp [show φ (MvPolynomial.C _)=_ from (φ).commutes a, coarse] -- an.sp
   | add p q hp hq=> intro y; rw [map_add,show p+q-(φ p+φ q)=p-φ p+(q-φ q) from by abel,← hf,map_add,add_mul]; rw [hf]; exact T.add_mem (hp _) (hq _)
   | mul_X p i hp=>
       let x:Push.Mark.Ink su:=⟨i.1,(Labels.axes su i.1).coord i.2⟩; have he: MvPolynomial.X i= Push.Mark.literal x.2:=Push.Mark.literal_x _
       obtain ⟨Y,Z,hY,hZ,hy,he',hf'⟩:=Push.Mark.split_literal x
       let a:=Push.Mark.literal x.2; change a - φ a=_ at he'
       intro y; rw [he,map_mul]; change coarse _ (p*a-(φ p)*(φ a))*_∈ T; rw [show p*a-φ p*φ a=(p-φ p)*φ a+(a-φ a)*p by ring,← hf, map_add]; rw [hf,coarse_at,coarse_at,add_mul,mul_assoc,mul_assoc,he']; exact T.add_mem (hp _) (h Y hy _)
lemma spinJobs (ξ : Covec d ⧸ slashEq d →ₗ[ℂ] Covec d) (he : (slashEq d).mkQ.comp ξ=LinearMap.id) (x:SpinPol d)(h :∀ t: Letters d,∀ y:Pol d,flora (Grass.line (petal t))*y∈T) : ∀ y:Pol d,flora (x-(ExteriorAlgebra.map ξ) (ExteriorAlgebra.map (slashEq d).mkQ x))*y∈T:=by
   let A:=ExteriorAlgebra.map (slashEq d).mkQ; let B:= ExteriorAlgebra.map ξ; obtain ⟨f,hf⟩:=floraL (d:=d)
   let M : Covec d → Covec d:= ξ ∘ (slashEq d).mkQ -- none
   have hi(v : Covec d) (g:v∈slashEq d) (y:Pol d): flora (Grass.line v)*y∈T:=by
       rw [garden] at g; refine Submodule.span_induction (p:=fun w _=>flora (Grass.line w)*y∈ T) ?_ ?_ ?_ ?_ g
       · rintro _ ⟨j,rfl⟩; exact h j _
       · simp [flora]
       · intro x y _ _ hx hy; rw [map_add, ← hf, map_add,add_mul]; rw [hf]; exact T.add_mem hx hy
       intro a x _ hx; rw [map_smul, ← hf, map_smul,_root_.smul_mul_assoc,hf]; exact T.smul_mem a hx
   have ht(u:List (Letters d))(p:Pol d): ∀ y:Pol d, flora ((u.map atom).prod-B (A (u.map atom).prod))*y∈T:=by -- NEED left move over B A atom; can strengthen head induction permit prefix sign & T multiples? hi for each equation factor left; moving X old head left multiplication of sum doesn't follow. strengthen right moving. telescope from suffix!
        induction u using List.reverseRecOn with
        | nil=> intro y; simp [flora]
        | append_singleton u i ih =>
           let b:= thetaBasis (Letters d) i; let x:= (u.map atom).prod
           let z:= atom i; have hu : B (A z)=Grass.line (M b):= by unfold A B z atom; simp only [Grass.line, ExteriorAlgebra.map_apply_ι]; rfl
           intro y; rw [List.map_append,List.prod_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,map_mul,map_mul]; have hh:b-M b∈slashEq d:= (Submodule.Quotient.mk_eq_zero _).mp (show (slashEq d).mkQ (b-M b)=0 by rw [map_sub, show (slashEq d).mkQ (M b)=(slashEq d).mkQ b from LinearMap.congr_fun he _,sub_self]); -- teleport x*(q) has q on right... commute B(A x) across q since grade line. Grass. Need lemma.
           change flora (x*z-B (A x)*B (A z))*y ∈ T
           have hZ: z-B (A z)=Grass.line (b-M b):=by rw [map_sub,hu]; rfl
           have hΒ: ∃ v:SpinPol d, x*Grass.line (b-M b)= Grass.line (b-M b)*v:=by
                -- x list prod grass.V
                apply ferry
           obtain ⟨v,hv⟩:=hΒ
           rw [show x*z-B (A x)*B (A z)= (x-B (A x))*B (A z) + x*(z-B (A z)) from by noncomm_ring, hZ,hv,←hf,map_add]; rw [hf,add_mul,flora_at,flora_at,mul_assoc,mul_assoc]; exact T.add_mem (ih _) (hi _ hh _)
   intro y
   rw [←hf]; rw [← Grass.write x] -- both x
   simp only [map_sum,map_smul, ← Finset.sum_sub_distrib, Finset.sum_mul,←smul_sub, _root_.smul_mul_assoc]
   refine Submodule.sum_mem T (fun i _=>?_); obtain ⟨F,-,-,hv⟩:=expression i; rw [hf,hv]; exact Submodule.smul_mem T _ (by simpa only [List.map_ofFn] using ht (List.ofFn F) y y)
 where
   ferry (v:Covec d)(l:List (Letters d)): ∃ w:SpinPol d,(l.map atom).prod*Grass.line v= Grass.line v*w:=by
       induction l with
       | nil=> exact ⟨1,by simp⟩
       | cons b l h=> obtain ⟨x,hx⟩:=h; refine ⟨-(atom b*x),?_⟩; rw [List.map_cons,List.prod_cons,mul_assoc,hx, ←mul_assoc,atom,line_line]; simp [mul_assoc]
-- final reduce lemma
lemma generative (p: Pol d) (hz:reduceEq p=0)(hG:∀ X:Push.Mark.Ink su, Push.Mark.Gap X→∀ y:Pol d, coarse d (Push.Mark.literal X.2)*y∈ T)(hS:∀ t: Letters d,∀ y:Pol d,flora (Grass.line (petal t))*y∈T): p∈ T:=by
   obtain ⟨ξ,hξ⟩:= (slashEq d).mkQ.exists_rightInverse_of_surjective (slashEq d).range_mkQ
   let A:=ExteriorAlgebra.map (slashEq d).mkQ; let B:= ExteriorAlgebra.map ξ; let C:=TensorProduct.map (draw su).toLinearMap B.toLinearMap; have hv (p:Pol d):p-C (reduceEq p)∈T:=by
       induction p using TensorProduct.induction_on with
       | zero=>simp
       | tmul x y=> rw [reduceEq,TensorProduct.map_tmul]; unfold C; rw [TensorProduct.map_tmul]; change x⊗ₜ[ℂ] y- draw _ (Maxwell.reduceEq _)⊗ₜ[ℂ] B (A y)∈_; rw [draw_erase]; let u:= φ x; let v:= B (A y); change x⊗ₜ[ℂ] y-u⊗ₜ[ℂ]v ∈T; rw [show x⊗ₜ[ℂ] y-u⊗ₜ[ℂ]v=(x-u)⊗ₜ[ℂ] v+x⊗ₜ[ℂ] (y-v) by rw [sub_tmul,tmul_sub]; abel, combo (x-u),combo' x]; exact T.add_mem (gaugeJobs T x hG _) (spinJobs T ξ hξ y hS _)
       | add x y hx hy=> rw [map_add,map_add]; convert! T.add_mem hx hy using 1; abel
   simpa only [hz,map_zero,sub_zero] using hv p
end YM.Massive.Elm
#print axioms YM.Massive.Elm.generative
