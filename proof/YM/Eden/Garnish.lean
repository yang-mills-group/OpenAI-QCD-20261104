import YM.Eden.Bea
/-! # degree filtered chart actually transports Taylor.V supports all ranks.Civic. -/
set_option autoImplicit false
noncomputable section
namespace YM.Eden
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior
open Finset Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free Bloom Arise Arise.Range Bloom.TreeP
open scoped Topology BigOperators InnerProductSpace Matrix Matrix.Norms.Frobenius TensorProduct Classical
variable {G:Gauge}{d k i m j:ℕ}{c f n:Side} {H:Bed}{t:Clip}{a b:ℝ}{I J :Type}[Fintype I][Fintype J]
open Massive UV QCD QCD.Eden QCD.Grass QCD.Bloom Lat Poised.Display
open Elm Elm.SparK Elm.SparK.Arbor Elm.SparK.Arbor.PrismD Poised Papyrus Lining Next.Rank.Normal Cylinder
open Poised.Plans RP YM.Source YM.Source.Drops
variable (U:Grid n)(x:Cover)(η:ℝ)(H:SourceRead.TaperHol)(K:Hol su) (hk:Drops.Peg K (d/2))
local notation "T"=> wide d 1
local notation "Y"=>(setas d ∘ₗ revere d)
local notation "SurV"=> Survey H
lemma pair_t (X W:Lily su d)(a b:SpinPol d) : (wide d η) ((X⊗ₜ[ℂ]a)*(W⊗ₜ[ℂ]b))=(wide d η) (X⊗ₜ[ℂ]a)*wide d η (W⊗ₜ[ℂ]b):=by
    funext n v; apply ContinuousMap.ext; intro U; rw [Algebra.TensorProduct.tmul_mul_tmul, wow,power_t,map_mul,map_mul]; change _=wide d η _ n _ _*wide d η _ n _ _; rw [wow,wow,power_t, power_t, smul_mul_assoc, mul_smul_comm, smul_smul]
lemma weld (p q:Bard d) : (wide d η) (p*q)=(wide d η) p*(wide d η) q:=by
   induction p using TensorProduct.induction_on with
   | zero=> simp
   | add x y h hp=> rw [add_mul,map_add,h,hp,map_add,add_mul]
   | tmul x y=>
     induction q using TensorProduct.induction_on with
     | zero=>simp
     | add x y h hp=> rw [mul_add,map_add,h,hp,map_add,mul_add]
     | tmul x y=>exact pair_t ..
lemma resp_mul(p q:Bard d)(i j g h:ℕ)(he: SurV (T p) i j (Y p))(hp: SurV (T q) g h (Y q)):SurV (T (p*q)) (i+g) (j+h) (Y (p*q)):=by
    have ht: revere d (p*q)=revere d p*revere d q:=by
        clear he hp
        induction p using TensorProduct.induction_on with
        | zero=>simp
        | add x y h hp=> rw [add_mul,map_add,map_add,h,hp,add_mul] -- he,hp deps -> ih takes hypothesis!
        | tmul x y=> induction q using TensorProduct.induction_on with
             | zero=>simp
             | add x y h hp=>rw[mul_add,map_add,map_add,h,hp,mul_add]
             | tmul a b=> unfold revere; simp only [Algebra.TensorProduct.tmul_mul_tmul,TensorProduct.map_tmul,AlgHom.toLinearMap_apply,map_mul]; rfl
    rw [weld,LinearMap.comp_apply, ht, ← fold_taps]; exact he.mul hp
lemma ardent : SurV (T 1) 0 0 (Y 1):=by
     have hx : T 1=(1:Drape):=funext fun n=> funext fun x=> ContinuousMap.ext (fun U=>by rw [wow]; change powerG d x U 1 ((1:Lily su d) ⊗ₜ[ℂ](1:SpinPol d))=_; rw [power_t,map_one,map_one,one_smul]; rfl)
     rw[hx]; change Survey H _ _ _ (setas d (revere _ (1⊗ₜ[ℂ]1))); rw [revere,TensorProduct.map_tmul, show (rollK su d).toLinearMap 1=1 from map_one (rollK ..)]; exact Survey.unit H d
include hk
lemma decor (l: List (Tube su d)) : Survey H (T ((l.map MvPolynomial.X).prod⊗ₜ[ℂ](1:SpinPol d))) l.length 0 (Y ((l.map MvPolynomial.X).prod⊗ₜ[ℂ](1:SpinPol d))) :=by
    induction l with
    | nil=>exact ardent H
    | cons p l h=>
       let T':=(l.map (MvPolynomial.X (R:=ℂ))).prod; have hp : (MvPolynomial.X p ⊗ₜ[ℂ](1:SpinPol d)) * (T'⊗ₜ[ℂ]1)=( (MvPolynomial.X p*T')⊗ₜ[ℂ]1):=by rw [Algebra.TensorProduct.tmul_mul_tmul,one_mul]
       have hz:= resp_mul H _ _ _ _ _ _ (germsG p H K hk) h; rw [hp] at hz; simp only [List.length_cons,Nat.add_comm l.length, List.map_cons,List.prod_cons]; exact hz
lemma skyline (l: List (Sings d)): Survey H (T ((1:Lily su d) ⊗ₜ[ℂ](l.map Grass.atom).prod)) 0 l.length (Y ((1:Lily su d)⊗ₜ[ℂ](l.map Grass.atom).prod)):=by
    induction l with
    | nil=>exact ardent H
    | cons p l h=>
       let S:=(l.map Grass.atom).prod; have hp: ((1:Lily su d)⊗ₜ[ℂ] Grass.atom p)*(1⊗ₜ[ℂ]S)=1⊗ₜ[ℂ] (Grass.atom p*S):=by rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one]
       obtain ⟨q,v,i,hp'⟩:= spots p; have hz:= resp_mul H _ _ _ _ _ _ (?_:SurV (T ((1:Lily su d)⊗ₜ[ℂ] Grass.atom p)) 0 1 (Y ((1:Lily su d)⊗ₜ[ℂ] Grass.atom p))) h; rw [hp] at hz; simp only [List.length_cons,Nat.add_comm l.length,List.map_cons,List.prod_cons]; exact hz
       rw[hp']; exact gemsS v i q H K
-- every finite expression.Det
abbrev countL (v: Tube G d →₀ℕ):ℕ:=∑ i∈v.support,v i
omit hk
lemma compost (v:Tube G d→₀ℕ) : ∃ L: List (Tube G d), L.length=countL v ∧ (L.map MvPolynomial.X).prod=MvPolynomial.monomial v (1:ℂ):=by
    classical
    -- Finset enumerate via powers; prove
    let p(i:Tube G d): Lily G d:= MvPolynomial.X i; have he(X: Finset (Tube G d)):∃ L:List (Tube G d), L.length=∑ i ∈X, v i ∧ (L.map p).prod=∏ i∈ X,p i^v i:=by
         induction X using Finset.induction_on with
         | empty=> refine ⟨[],?_,?_⟩ <;> simp
         | insert i s hi ih=> obtain ⟨L,hL,h⟩:=ih; exact ⟨(List.replicate (v i) i)++L,by simp [hL,hi], by simp [h,hi]⟩
    obtain ⟨L,hL,h⟩:= he v.support; rw [MvPolynomial.monomial_eq]; exact ⟨L,hL, by rw [map_one,one_mul]; exact h⟩
include hk
lemma moneyRoot (p: Grimo d) : SurV (T (sketch p)) (countL p.1) p.2.card (Y (sketch p)) :=by
    obtain ⟨L,hL,hP⟩:=compost p.1; obtain ⟨A,-,-,hA⟩:=Grass.expression p.2; let M:= List.ofFn A; have he:M.length=p.2.card:=List.length_ofFn; have ht : sketch p=((L.map MvPolynomial.X).prod ⊗ₜ[ℂ](1:SpinPol d))*((1:Lily su d) ⊗ₜ[ℂ](M.map Grass.atom).prod):=by rw [Algebra.TensorProduct.tmul_mul_tmul,hP,mul_one,one_mul,List.map_ofFn]; exact congr_arg _ hA
    have hz:=resp_mul H _ _ _ _ _ _ (decor H K hk L) (skyline H K hk M); rw [← ht,hL,he,add_zero,zero_add] at hz; exact hz
lemma chart (p:Bard d)(h:p ∈ Rgl d i m j): SurV (T p) m j (Y p):=by
     refine Submodule.span_induction (p:=fun p _=> SurV (T p) m j (Y p)) ?_ (by rw[map_zero,map_zero]; exact Survey.dry ..) (fun x y _ _ hx hy=>by rw [map_add,map_add]; exact hx.add hy) (fun s x _ h=>by rw [map_smul,map_smul]; exact h.scale s) h
     rintro x ⟨p,h,rfl⟩; change tagwt p=_ at h; have hp:m=countL p.1:=by have ht:= (congr_arg (Prod.snd ∘ Prod.fst) h).symm; unfold tagwt at ht; dsimp only [Function.comp_apply] at ht; rw [Finsupp.weight_apply,Finsupp.sum,Prod.snd_sum] at ht; simpa [legwt] using ht -- term
     rw [hp,show j=p.2.card from (congr_arg Prod.snd h).symm]; exact moneyRoot H K hk p
end YM.Eden
#print axioms YM.Eden.chart
