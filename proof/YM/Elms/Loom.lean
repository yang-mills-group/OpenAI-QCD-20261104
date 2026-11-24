import YM.Elms.Graded
/-!
# Euclidean profiles and massless coefficient spread. Any single-site avoidance.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Topology BigOperators TensorProduct Pointwise Classical ContDiff
variable {d:ℕ}
open Papyrus.Purl Papyrus
local notation "V"=>Covec d
noncomputable def trow (q:Bool)(p:Multi d)(i:Fiber)(v: Flavor 6): Covec d:=if q then Grass.thetaBasis (Letters d) (Sum.inr ((p,i),v)) else Grass.thetaBasis (Letters d) (Sum.inl ((p,i),v))
noncomputable def bphy (q:Bool)(p:Multi d)(i:Fiber)(v:Flavor 6):SpinPol d:=Grass.line (trow q p i v)
noncomputable def lineT (q:Bool) {M : Type} [Fintype M](i : M) : Dirac M:= if q then bar i else psi i
lemma timely (q:Bool)(p:Multi d)(i:Fiber)(v:Flavor 6): bphy q p i v=lineT q ((p,i),v):=by cases q <;> rfl
def sings(p:Multi d)(x:E4):ℂ:=∏ i:Axis,(x i:ℂ)^power p i / Nat.factorial (power p i)
lemma sing_cover(p:Multi d)(x:Cover) : sings p (vector x)=(profileL p x:ℂ):=by unfold sings vector profileL ψ; simp
lemma sing_coe(p:Multi d)(x:E4)(h:ℝ): sings p (h • x)=(h:ℂ)^(UV.order (power p))*sings p x:=by unfold sings; simp only [PiLp.smul_apply,Complex.ofReal_mul,smul_eq_mul, mul_pow, mul_div_assoc, Finset.prod_mul_distrib,prod_pow_eq_pow_sum]; rfl
lemma sing_scale(p:Multi d)(x:Cover)(h:ℝ) : SourceRead.profile p x h=(h:ℂ)^spinWeight p*sings p (vector x):=by unfold SourceRead.profile sings vector; push_cast; rfl
noncomputable def twig (q:Bool)(i:Fiber)(u:Flavor 6)(z:E4) : V:=∑ p:Multi d,sings p z • trow q p i u
lemma twigD (q:Bool)(i:Fiber)(u:Flavor 6)(p:Multi d):
    trow q p i u=∑ x∈Lattice.box d,(sample p x:ℂ) • twig (d:=d) q i u (vector x):=by
        unfold twig; simp_rw [Finset.smul_sum,smul_smul,sing_cover]; rw [Finset.sum_comm]; simp_rw [← Complex.ofReal_mul,←sum_smul,← Complex.ofReal_sum,sample_Φ]; simp -- namespace box
-- any-away span. show missed ONE address by line polynomial in coordinate far excludes
lemma twig_safe (q:Bool)(i:Fiber)(u:Flavor 6)(b:Cover) (p:Multi d): trow q p i u∈Submodule.span ℂ {y | ∃ x:Cover,x≠b ∧ twig q i u (vector x)=y}:=by
   let P:=Submodule.span ℂ {y:V | ∃ x:Cover,x≠b∧ twig q i u (vector x)=y}; have ht(x)(hx:x≠b): P.mkQ (twig q i u (vector x))=0:=(Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨x,hx,rfl⟩)
   have hb : P.mkQ (twig q i u (vector b))=0:=by
       let W:= V ⧸ P; let Q:=Module.finBasis ℂ W; apply Q.equivFun.injective; funext k
       let f:V→ₗ[ℂ]ℂ:= (Q.coord k).comp P.mkQ; change f _= _ ; suffices he:f (twig q i u (vector b))=0 by simp only [map_zero, Pi.zero_apply]; exact he
       -- interpolation via finite tooth spacing with shift.E. use polynomial
       let a:Axis:=0; let g (n:ℤ):Cover:= update b a (b a+n)
       let L(j:Axis):Polynomial ℂ:= if a=j then Polynomial.C ((b j:ℤ):ℂ) + Polynomial.X else Polynomial.C ((b j:ℤ):ℂ)
       let S(w:Multi d):Polynomial ℂ:= ∏ j:Axis,(L j)^power w j * Polynomial.C ((↑(Nat.factorial (power w j)):ℂ)⁻¹)
       let A:Polynomial ℂ:=∑ W:Multi d,S W*Polynomial.C (f (trow q W i u))
       have hg (n:ℤ)(j:Axis): (L j).eval (n:ℂ)=(↑((g n j)):ℂ):=by unfold L g; by_cases h:j=a<;> simp [*,Ne.symm]
       have hA(n:ℤ): A.eval (n:ℂ)=f (twig q i u (vector (g n))):=by
           unfold A twig S; simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_prod,Polynomial.eval_pow,hg,map_sum,map_smul]; simp only [sings,vector,div_eq_mul_inv,WithLp.ofLp_toLp,Complex.ofReal_intCast,smul_eq_mul] -- typeclasses
       have hZ(n:ℤ)(hn:n≠0): A.eval (n:ℂ)=0:=by rw [hA]; change Q.coord _ (P.mkQ _)=0; rw [ht _ (fun he=>hn (by simpa [g] using congr_fun he a)),map_zero]
       have h0:A=0:= by
           by_contra hx
           have hQ : (Finset.range 0).card=0:=by simp
           let f(n:ℕ):ℂ:=↑((↑(n+1):ℤ)); have hc:Set.Infinite (Set.range f):= Set.infinite_range_of_injective (fun x y h=> by unfold f at h; exact Nat.succ_inj.mp (by exact_mod_cast h))
           apply hc; apply Set.Finite.subset A.roots.toFinset.finite_toSet; rintro _ ⟨n,rfl⟩; exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hx).mpr (hZ _ (by exact_mod_cast (Nat.succ_pos n).ne')))
       rw [← show g 0=b by unfold g; simp, ←hA,h0]; simp
   apply (Submodule.Quotient.mk_eq_zero _).mp
   change P.mkQ (trow q p i u)=0; rw [twigD q i u p,map_sum]; refine Finset.sum_eq_zero fun x _=>?_ ; rw [map_smul]; cases eq_or_ne x b with
   | inl he=> simp only [he,hb,smul_zero]
   | inr he=> simp only [ht x he,smul_zero]
end YM.Massive.Elm
#print axioms YM.Massive.Elm.twig_safe
