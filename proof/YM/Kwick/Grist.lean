import YM.Kai.Apes
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open Filter Function Set Lattice Wilson RG Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Poised Poised.Beacon Poised.Display Poised.Stative Poised.Sieve
open Finset Tawny Tawny.Cast Tawny.Cast.Rays Tawny.Cast.Carnal Tawny.Cast.Perla Tawny.Cast.TableT Tawny.Cast.Zinc
open Oriole
local notation "D"=>10
local notation "T"=>Grade
local notation "L"=> (0:Multi 10)
noncomputable def tierQ : Fin 4→ Grade:= ![(8,0,2),(10,0,2),(10,1,2),(10,2,0)]
variable (x:Grade)
local notation "P"=> kind 10 x
local notation "sK" k:arg=> if k=x then (1:ℂ) else 0
-- useful coefficients
lemma pairBill (i j: SpinMode 10) (M:Labels.Key su→₀ℕ) : let p:= MvPolynomial.monomial M (1:ℂ); let f:=p⊗ₜ[ℂ] (bar i*psi j); (kind 10 x) f=(sK (2*Labels.height M + (spinWeight i.1.1+spinWeight j.1.1), life M,2)) • f:=by
      intro p f; let a:= Sum.inr (α:=SpinMode 10) i; let b:= Sum.inl (β:=SpinMode 10) j; let u:PowerPair 10:=(M,{a,b}); have hp:a ≠ b:=by intro h; unfold a b at h; cases h
      have hh:P (gen u)=(sK (crest u)) • gen u:=by rw [kind_gate]; split <;>simp[*]
      have he: crest u=(2*Labels.height M+(spinWeight i.1.1+spinWeight j.1.1),life M, 2):=by
          unfold u crest UV.weight; simp only [Finset.sum_pair hp, card_pair hp]; rfl
      rw [he] at hh; change (P) (p⊗ₜ[ℂ](atom a*atom b))=(if _ then (1:ℂ) else 0) • _; unfold f bar psi; rcases bladeX a b hp with h|h
      · rw [show atom a * atom b=mono {a,b} from h]; exact hh -- rw RHS defin
      rw [show atom a*atom b= -mono {a,b} from h]; change P (p⊗ₜ[ℂ] (-mono _)) = _ • (p⊗ₜ[ℂ] _); rw[TensorProduct.tmul_neg,map_neg ,smul_neg]; exact congr_arg Neg.neg hh
lemma form_height (a b:Flavor 6)(p q:Multi 10)(M:Spike): P (bilinear a b M p q)= (sK (spinWeight p+ spinWeight q,0,2)) • bilinear a b M p q:=by
      unfold bilinear; simp_rw [TensorProduct.tmul_sum,TensorProduct.tmul_smul,map_sum,map_smul,Finset.smul_sum]
      refine sum_congr rfl (fun i _=>sum_congr rfl fun j _=>sum_congr rfl fun k _=>?_)
      let f:=(bar ((p,i,k),a)*psi ((q,j,k),b)); have hh:=pairBill x ((p,i,k),a) ((q,j,k),b) 0; dsimp only at hh; simp only [MvPolynomial.monomial_zero',map_one,life,Finsupp.support_zero, sum_empty, Labels.height,map_zero,mul_zero,zero_add] at hh
      rw [hh]; exact smul_comm ..
-- med shape from yard + coat. via matrix shards
set_option maxHeartbeats 800000 in
lemma chillS (i j:Axis)(a:Flavor 6)(B:Spike) : P (youthL a i j B)=(sK (tierQ 2)) • youthL a i j B:=by
      unfold youthL; rw [map_sum,smul_sum]; refine sum_congr rfl fun k _=>?_ ; let p:Labels.Key su:= ⟨0,k⟩; let t:Finsupp _ ℕ:= Finsupp.single p 1; let F: GPol:= MvPolynomial.X p
      let u(v:Fiber):SpinMode 10:= ((0,v),a); let W:= whirl (StressFlux.curl0 i j (Labels.axes su 0 k)) B -- order curl
      have hv: weave a B i j (Labels.axes su 0 k)= ∑ i: Fiber,∑ j:Fiber, (W i j) • Matrix.single (u i) (u j) (1:ℂ):=by
           change (∑ i:Fiber, ∑ j:Fiber, Matrix.single (u i) (u j) (W i j))= _; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ext x y; simp only [Matrix.single, Matrix.of_apply, Matrix.smul_apply,smul_eq_mul]; split <;> simp
      rw [hv]; simp_rw [map_sum,map_smul, Tawny.simple_single,TensorProduct.tmul_sum,TensorProduct.tmul_smul,map_sum,map_smul,smul_sum]; refine sum_congr rfl (fun i _=>sum_congr rfl fun j _=>?_); have hg:=pairBill x (u i) (u j) t; dsimp only at hg
      have ht: Labels.height t=2:=by unfold t Labels.height; rw [Finsupp.weight_single]; rfl
      have he :life t=1:=by simp [life,t]
      rw[ht,show (u i).1.1=L from rfl,cost_root,he] at hg
      rw [show (P (F⊗ₜ[ℂ] _))=_ from hg]; exact smul_comm ..
lemma phosphor (i j k l m:Axis): P (GE i j k l m).val=(sK (tierQ 3)) • (GE i j k l m).val:=by
     let v: Labels.Label su 5:= StressFlux.pairDeriv su i j k l m; let f:= plain 10; let s:ℂ:=sK (tierQ 3); change P (f v.val)=s • f v.val
     have hp :Labels.pureDegree v.val 5 2:= StressFlux.productPol_grade ..
     have hv : v.val=∑ i∈ v.val.support, MvPolynomial.monomial i (MvPolynomial.coeff i v.val):=(MvPolynomial.support_sum_monomial_coeff _).symm
     rw [hv,map_sum,map_sum,smul_sum]; refine sum_congr rfl fun t ht=>?_ ; have hh:=hp (MvPolynomial.mem_support_iff.mp ht); rw [Labels.weight_slot] at hh
     let i:= MvPolynomial.coeff t v.val; have he: crest (d:=10) (t,∅)=tierQ 3:=by
           have h1:Labels.height t=5:=congr_arg Prod.fst hh; have hz:life t=2:=congr_arg Prod.snd hh
           simp only [crest,UV.weight,h1,hz,sum_empty,Finset.card_empty]; rfl
     let g:= gen (d:=10) (t,∅); rw [show f (MvPolynomial.monomial t i)= i • g from ?_]; rw [map_smul,show P g= s • g from ?_, smul_comm]
     · unfold g; rw[kind_gate,he]; unfold s; split_ifs <;> simp
     unfold f g gen; rw [Perla.plainP, Grass.mono_empty, TensorProduct.smul_tmul', show i • MvPolynomial.monomial t 1= MvPolynomial.monomial t i from by rw [← map_smul,smul_eq_mul,mul_one]] -- orientation
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.phosphor
